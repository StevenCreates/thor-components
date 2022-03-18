import React from "react";
import PropTypes from "prop-types";
import "./button.css";
import { css } from "@mxenabled/cssinjs";

export const BUTTON_VARIANTS = {
  PRIMARY: 'primary',
  NEUTRAL: 'neutral',
  TRANSPARENT: 'transparent',
  TRANSPARENT_TERTIARY: 'transparent-tertiary',
  LINK: 'link',
  LINK_TERTIARY: 'link-tertiary',
  LINK_DESTRUCTIVE: 'link-destructive',
  DESTRUCTIVE: 'destructive',
}

export const BUTTON_SIZES = {
  LARGE: 'large',
  SMALL: 'small',
}

export const COLOR = {
  PRIMARY: '#1E293B',
  PRIMARY_HOVER: '#4a5362',
  PRIMARY_DISABLED: '#616975'
}

export const TEXT_COLOR = {
  PRIMARY: '#FFFFFF'
}


export const Button = ({
  children,
  className = "",
  disabled,
  onClick,
  size,
  variant = BUTTON_VARIANTS.PRIMARY,
  ...rest
}) => {
  const styles = getStyles(disabled);
  return (
    <button
      aria-disabled={disabled}
      className={`${styles} thor-button thor-${variant} ${className}`}
      onClick={!disabled ? onClick : (e) => e.preventDefault()}
      type="button"
      {...rest}
    >
      {children}
    </button>
  );
};

const getStyles = (disabled) =>
  css({
    display: 'flex',
    alignItems: 'center',
    justifyContent: 'center',
    border: 'none',
    borderRadius: '6px',
    cursor: disabled ? 'not-allowed' : 'pointer',
    whiteSpace: 'nowrap',
    fontSize: '12px',
    position: 'relative',
    padding: `0px 12px`,
    margin: 0,
    width: 'auto',
    height: '30px',
    transition: `all 6ms easing`,
    '&:focus': {
      outline: 'none',
      boxShadow: 'blue 2px',
    },
    [`&.thor-${BUTTON_VARIANTS.PRIMARY}`]: {
      backgroundColor: COLOR.PRIMARY,
      color: TEXT_COLOR.PRIMARY,
      '&:hover': !disabled && {
        backgroundColor: COLOR.PRIMARY_HOVER,
        color: TEXT_COLOR.PRIMARY,
      },
      ...(disabled && {
        backgroundColor: COLOR.PRIMARY_DISABLED,
        color: TEXT_COLOR.PRIMARY,
      }),
    },
  });

  Button.propTypes = {
    className: PropTypes.string,
    disabled: PropTypes.bool,
    onClick: PropTypes.func,
    size: PropTypes.oneOf(Object.values(BUTTON_SIZES)),
    variant: PropTypes.oneOf(Object.values(BUTTON_VARIANTS)),
  }

Button.defaultProps = {
  backgroundColor: null,
  primary: false,
  size: "medium",
  onClick: undefined,
};
