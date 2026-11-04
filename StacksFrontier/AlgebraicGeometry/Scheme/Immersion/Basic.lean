module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Immersions and subschemes of schemes

An open or closed immersion of schemes is an immersion of the corresponding kind on locally
ringed spaces. Open subschemes are restrictions to open sets, closed subschemes are cut out by
ideal sheaves, and a locally closed immersion is one that factors as a closed immersion followed
by an open immersion.

All five parts are already available in Mathlib at hypotheses no stronger than the source's, so
this file records the identifications rather than restating them.

## Main results

The source's five parts are, in order, `AlgebraicGeometry.IsOpenImmersion`; the open-subscheme
triple `AlgebraicGeometry.Scheme.Opens`, `.toScheme` and `.ι`;
`AlgebraicGeometry.IsClosedImmersion`; the closed-subscheme triple
`AlgebraicGeometry.Scheme.IdealSheafData`, `.subscheme` and `.subschemeι`; and
`AlgebraicGeometry.IsImmersion` together with its factorization criterion
`AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`.

## Implementation notes

Open immersions of schemes are definitionally open immersions of locally ringed spaces. An open
subscheme is represented by an open set together with its restricted scheme structure and
inclusion, rather than by an abstract morphism with open image. For closed subschemes,
`IdealSheafData` packages an ideal sheaf on a scheme and `subscheme`, `subschemeι` give its
scheme and closed inclusion; this is the scheme-level form of the closed-subspace construction
for locally ringed spaces. Mathlib's closed-immersion predicate asks for a closed embedding that
is surjective on stalks, and the ideal-sheaf condition that the general theory of closed
immersions of locally ringed spaces carries is automatic for schemes.

## References

* [Stacks Project, Tag 01IO](https://stacks.math.columbia.edu/tag/01IO)
-/

public section

add_to_stacks 01IO "part (1): open immersions" AlgebraicGeometry.IsOpenImmersion
add_to_ega "I 4.2.1" AlgebraicGeometry.IsOpenImmersion
add_to_stacks 01IO "part (2): open subsets" AlgebraicGeometry.Scheme.Opens
add_to_sga "1 IX 2.3" AlgebraicGeometry.Scheme.Opens
add_to_sga "1 VIII 4.4" AlgebraicGeometry.Scheme.Opens
add_to_sga "4 VII 4.2.2" "partial" AlgebraicGeometry.Scheme.Opens
add_to_stacks 01IO "part (2): restricted scheme" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_sga "2 XII 4.1" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "I 10.4.4" "special case" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "I 2.1.7" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "I 2.2.10" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "I 2.2.3" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "I 4.1.3" "special case" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "IV 4.5.3" "partial" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "IV 4.9.6" "partial" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "IV 9.6.7" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_ega "IV 9.7.11" "more general" AlgebraicGeometry.Scheme.Opens.toScheme
add_to_stacks 01IO "part (2): inclusion" AlgebraicGeometry.Scheme.Opens.ι
add_to_sga "1 XIII 2.1.0" AlgebraicGeometry.Scheme.Opens.ι
add_to_sga "2 XII 4.1" AlgebraicGeometry.Scheme.Opens.ι
add_to_sga "4 XVI 3.1" "more general" AlgebraicGeometry.Scheme.Opens.ι
add_to_ega "I 2.2.3" AlgebraicGeometry.Scheme.Opens.ι
add_to_ega "I 4.1.7" "special case" AlgebraicGeometry.Scheme.Opens.ι
add_to_ega "I 4.2.1" AlgebraicGeometry.Scheme.Opens.ι
add_to_stacks 01IO "part (3): closed immersions" AlgebraicGeometry.IsClosedImmersion
add_to_sga "3 IV 4.7" AlgebraicGeometry.IsClosedImmersion
add_to_ega "I 4.2.1" AlgebraicGeometry.IsClosedImmersion
add_to_stacks 01IO "part (4): ideal sheaves" AlgebraicGeometry.Scheme.IdealSheafData
add_to_stacks 01IO "part (4): closed subscheme" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_sga "3 III 4.5.0" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "I 10.14.2" "partial" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "I 4.1.2" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "I 4.1.3" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "I 5.1.9" "more general" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "II 4.6.15" "more general" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "II 8.13.4" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "III 5.3.5" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "IV 21.15.3.3" "more general" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "IV 21.2.12" "more general" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "IV 21.6.5" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_ega "IV 4.5.3" "partial" AlgebraicGeometry.Scheme.IdealSheafData.subscheme
add_to_stacks 01IO "part (4): inclusion" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_sga "1 III 7.1" "partial" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_sga "3 III 4.5.0" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_ega "I 4.1.7" "special case" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_ega "I 5.1.9" "more general" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_ega "II 4.6.15" "more general" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_ega "II 8.13.4" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_ega "III 4.1.3" "canonical immersion i_k" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_ega "IV 21.15.3.3" "more general" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_ega "IV 21.2.12" "more general" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_ega "IV 21.6.5" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι
add_to_stacks 01IO "part (5): locally closed immersions" AlgebraicGeometry.IsImmersion
add_to_sga "3 IV 4.7" "partial" AlgebraicGeometry.IsImmersion
add_to_ega "I 4.2.1" AlgebraicGeometry.IsImmersion
add_to_stacks 01IO "part (5): factorization" AlgebraicGeometry.IsImmersion.isImmersion_iff_exists
add_to_sga "6 0 2.1" "special case" AlgebraicGeometry.IsImmersion.isImmersion_iff_exists
add_to_ega "I 4.2.1" AlgebraicGeometry.IsImmersion.isImmersion_iff_exists

end
