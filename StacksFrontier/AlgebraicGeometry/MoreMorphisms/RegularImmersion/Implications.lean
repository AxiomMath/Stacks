module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Germ
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.QuasiRegular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.RegularToQuasiRegular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.StalkBridge
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksCore.Tactic.StacksAttribute

/-!
# Regular implies Koszul-regular implies `H₁`-regular implies quasi-regular

For an immersion of schemes, regularity implies Koszul-regularity, which implies `H₁`-regularity,
which in turn implies quasi-regularity.  This is Stacks tag 063K, and the corresponding chain of
implications between the four conditions of Stacks tag 063D on a sheaf of ideals is Stacks tag
063E.

All four conditions on an ideal sheaf `J` ask that near every point of the support of `O_X / J`
the ideal be generated on an open `U` by a family of sections which is, respectively, a regular, a
Koszul-regular, an `H₁`-regular or a quasi-regular sequence on `U`.  The same open and the same
family therefore serve throughout, and each implication between the ideal-sheaf conditions is
exactly the corresponding implication between the conditions on a family of sections.

Those are in turn ring-theoretic, through the germs.  All four sequence conditions are stated
germwise:
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isWeaklyRegular_germFamily_of_isRegularSequenceOn`
turns regularity of a family of sections over `U` into weak regularity of its germ sequences,
`RegularIdealSheaf.isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular` and
`RegularIdealSheaf.isKoszulSequenceExactOn_iff_forall_germ_isH1Regular`
identify Koszul exactness in positive degrees and in degree `1` with `Koszul.IsKoszulRegular` and
`Koszul.IsH1Regular` of those germ sequences, and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegularMapIso_iff_forall_germ` does the same for
the quasi-regularity morphism of Stacks tag 063B.  So the chain is the ring-level chain of Stacks
tags 062F and 062I applied stalk by stalk.

Stacks tag 063C is also proved for the *other* rendering of the two middle conditions, the one
which reads them off the Koszul complex of sheaves rather than germwise:
`Stacks.AlgebraicGeometry.SeqKoszul.isKoszulRegularSequence_iff_forall_germ` and
`Stacks.AlgebraicGeometry.SeqKoszul.isH1RegularSequence_iff_forall_germ` are the corresponding
bridges to the ring level, and the ring-level chain of Stacks tags 062F and 062I is applied
through them in exactly the same way.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulSequenceExactOn_of_isRegularSequenceOn`: the
  Koszul complex of a regular sequence of sections is acyclic in positive degrees.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isIso_quasiRegularMap_of_isKoszulSequenceExactOn`:
  if the Koszul complex of a family of sections is exact in degree `1`, the quasi-regularity
  morphism of Stacks tag 063B is an isomorphism.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularSequence_of_regularSequence` and
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isIso_quasiRegularMap_of_isH1RegularSequence`: the
  outer two implications of **Stacks tag 063C**, for a family of global sections of the structure
  sheaf and for the sheaf Koszul complex.  The middle one is
  `Stacks.AlgebraicGeometry.SeqKoszul.isH1RegularSequence_of_isKoszulRegularSequence`, where the
  two sheaf Koszul conditions are defined.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularSequence_of_isRegularSequenceOn`: the
  same first implication for a family of sections over an open, read on the restriction.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularIdealSheaf_of_isRegularIdealSheaf`
  and
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegularIdealSheaf_of_isH1RegularIdealSheaf`:
  two of the implications of Stacks tag 063E, for parts (1)–(4) of Stacks tag 063D.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_isRegularImmersion`,
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isH1RegularImmersion_of_isKoszulRegularImmersion`
  and
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegularImmersion_of_isH1RegularImmersion`:
  **Stacks tag 063K.**  They are stated for the four conditions on an immersion as Stacks tag
  063J defines them, so that each is the condition carrying that tag and no second spelling of
  any of them is introduced.

## Implementation notes

**No Noetherian and no quasi-coherence hypothesis is needed**, because only the implications are
proved, not the equivalences: the converse of the outer implication is the half of Stacks tag 063I
that needs them.

**Weak regularity, not `RingTheory.Sequence.IsRegular`, is what the stalks supply.** Regularity of
an ideal sheaf says nothing about the generated ideal being proper, so the germwise form of part
(1) of Stacks tag 063D yields exactly the nonzerodivisor condition on germs, i.e. weak regularity
in each stalk;  Stacks tag 062F is applied in the form that accepts it.

**No stalk is transported across a restriction for the germwise conditions.** Each of the four
conditions on a family of sections over `U` has a germwise form phrased with the germs of `X`
itself at points of `U`, so the ring-level implications are applied in the stalks of `X` and no
comparison between the stalks of `X` and those of `X` restricted to `U` enters.

**Two renderings of Koszul- and `H₁`-regularity of a family of sections are both in play, and
each implication is proved for the one its conclusion is stated with.**  The ideal-sheaf
conditions of Stacks tag 063D are formalized germwise, by
`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulSequenceExactOn`, whereas Stacks tag 063C is
about the Koszul complex of sheaves, so the implications between the conditions on a *sequence*
are also stated with `Stacks.AlgebraicGeometry.SeqKoszul.IsKoszulRegularSequence` and
`Stacks.AlgebraicGeometry.SeqKoszul.IsH1RegularSequence`, the vanishing of the homology of that
complex.  The two agree — that is
`Stacks.AlgebraicGeometry.SeqKoszul.isKoszulRegularSequence_iff_forall_germ` together with
`Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictStalkEquiv` — but neither is the other on the
nose, so each implication below reaches the ring level directly rather than through the
comparison.

**For the sheaf Koszul complex over an open, the germ sequences are compared across the
restriction.**  Koszul-regularity of a family of sections of `U` in the sense of
`Stacks.AlgebraicGeometry.SeqKoszul.IsKoszulRegularSequence` is a condition on the ringed space
`X` restricted to `U`, whose stalks are the stalks of `X` at points of `U` but not on the nose:
they are identified by
`Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictStalkEquiv`.  Weak regularity is moved across
that ring isomorphism by `Stacks.AlgebraicGeometry.isWeaklyRegular_ofFn_map_of_flat`, a ring
isomorphism being flat, rather than by a transport of the Koszul complex.

## References

* [Stacks Project, Lemma 31.21.2 (Tag 063K)](https://stacks.math.columbia.edu/tag/063K)
* [Stacks Project, Lemma 31.21.1 (Tag 063C)](https://stacks.math.columbia.edu/tag/063C)
* [Stacks Project, Lemma 31.20.2 (Tag 063E)](https://stacks.math.columbia.edu/tag/063E)
* [Stacks Project, Lemma 15.30.2 (Tag 062F)](https://stacks.math.columbia.edu/tag/062F)
* [Stacks Project, Lemma 15.30.5 (Tag 062I)](https://stacks.math.columbia.edu/tag/062I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.RingTheory.QuasiRegular
open Stacks.RingTheory.RegularIdealSheaf
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

/-- The two spellings of the sequence of germs of a family of global sections agree. -/
private theorem germSequence_eq (X : RingedSpace.{u, u}) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op (⊤ : Opens X))) (x : X) :
    Stacks.RegularSequence.germSequence X f x = germSequence X f x := rfl

/-- A family whose list is weakly regular is Koszul-regular. -/
private theorem isKoszulRegular_of_isWeaklyRegular_ofFn {A : Type*} [CommRing A] {r : ℕ}
    {f : Fin r → A} (h : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f)) :
    Koszul.IsKoszulRegular f :=
  (Koszul.isKoszulRegularOn_self_iff _).mp
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1 h)

section Sequences

variable (X : RingedSpace.{u, u})

/-- **A regular sequence of sections is a Koszul-regular sequence.**  This is the first implication
of Stacks tag 063C, in the form the ideal-sheaf conditions of Stacks tag 063D use. -/
theorem isKoszulSequenceExactOn_of_isRegularSequenceOn (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (h : IsRegularSequenceOn X U f) :
    IsKoszulSequenceExactOn X U f (fun j => 0 < j) :=
  (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular X U f).mpr fun y hy =>
    isKoszulRegular_of_isWeaklyRegular_ofFn
      (isWeaklyRegular_germFamily_of_isRegularSequenceOn X U f h y hy)

/-- **For a family of sections whose Koszul complex is exact in degree `1` the quasi-regularity
morphism of Stacks tag 063B is an isomorphism.**  This is the implication of Stacks tag 062I read
on a ringed space. -/
theorem isIso_quasiRegularMap_of_isKoszulSequenceExactOn (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (h : IsKoszulSequenceExactOn X U f (fun j => j = 1)) :
    IsIso (quasiRegularMap (X.restrict U.isOpenEmbedding)
      (fun i => sectionOnRestriction X U (f i))).hom :=
  (isQuasiRegularMapIso_iff_forall_germ X U f).mpr fun y hy =>
    (isQuasiRegularRel_iff_bijective _).mpr
      ((isQuasiRegular_ofFn_iff _).mp
        (Koszul.isQuasiRegular_of_isH1RegularOn
          ((Koszul.isH1RegularOn_self_iff _).mpr
            ((isKoszulSequenceExactOn_iff_forall_germ_isH1Regular X U f).mp h y hy))))

/-- **A regular sequence of sections is a Koszul-regular sequence**, in the sense that the Koszul
complex of sheaves of the family read on `X` restricted to `U` is acyclic in positive degrees.
This is the first implication of Stacks tag 063C for a family of sections over an open. -/
theorem isKoszulRegularSequence_of_isRegularSequenceOn (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (h : IsRegularSequenceOn X U f) :
    SeqKoszul.IsKoszulRegularSequence (X.restrict U.isOpenEmbedding)
      (fun i => sectionOnRestriction X U (f i)) := by
  rw [SeqKoszul.isKoszulRegularSequence_iff_forall_germ]
  rintro ⟨y, hy⟩
  have hw := isWeaklyRegular_germFamily_of_isRegularSequenceOn X U f h y hy
  have hflat : RingHom.Flat ((restrictStalkEquiv X U y hy).symm :
      X.presheaf.stalk y →+*
        (X.restrict U.isOpenEmbedding).presheaf.stalk (⟨y, hy⟩ : ↥U)) :=
    RingHom.Flat.of_bijective (restrictStalkEquiv X U y hy).symm.bijective
  have hmap := isWeaklyRegular_ofFn_map_of_flat ((restrictStalkEquiv X U y hy).symm :
      X.presheaf.stalk y →+*
        (X.restrict U.isOpenEmbedding).presheaf.stalk (⟨y, hy⟩ : ↥U)) hflat
      (germFamily X U f y hy) hw
  have hfam : (fun i => ((restrictStalkEquiv X U y hy).symm :
        X.presheaf.stalk y →+*
          (X.restrict U.isOpenEmbedding).presheaf.stalk (⟨y, hy⟩ : ↥U))
        (germFamily X U f y hy i)) =
      Stacks.RegularSequence.germSequence (X.restrict U.isOpenEmbedding)
        (fun j => sectionOnRestriction X U (f j)) (⟨y, hy⟩ : ↥U) := by
    funext i
    exact ((restrictStalkEquiv X U y hy).symm_apply_eq).mpr
      (restrictStalkEquiv_germSequence X U f y hy i).symm
  rw [hfam] at hmap
  exact isKoszulRegular_of_isWeaklyRegular_ofFn hmap

/-- A regular sequence of global sections of the structure sheaf is a Koszul-regular sequence: if
multiplication by `f i` on `O_X/(f₁, …, f_{i-1})` is an injective map of sheaves for every `i`,
then the Koszul complex `K_•(O_X, f_•)` is acyclic in positive degrees. -/
@[stacks 063C "regular implies Koszul-regular", ega "IV 19.5.1" "a) => b)"]
theorem isKoszulRegularSequence_of_regularSequence {r : ℕ}
    (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))
    (hf : ∀ i : Fin r, Mono (regularSequenceMultiplication X f i).multiplication) :
    SeqKoszul.IsKoszulRegularSequence X f := by
  rw [SeqKoszul.isKoszulRegularSequence_iff_forall_germ]
  intro x
  exact isKoszulRegular_of_isWeaklyRegular_ofFn
    (isWeaklyRegular_germSequence_of_forall_mono X f hf x)

/-- For an `H₁`-regular sequence of global sections the quasi-regularity morphism of Stacks tag
063B is an isomorphism, i.e. the sequence is quasi-regular. -/
@[stacks 063C "H₁-regular implies quasi-regular"]
theorem isIso_quasiRegularMap_of_isH1RegularSequence {r : ℕ}
    (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))
    (h : SeqKoszul.IsH1RegularSequence X f) : IsIso (quasiRegularMap X f).hom := by
  rw [isIso_quasiRegularMap_hom_iff]
  intro x
  have hx : Koszul.IsH1Regular (germSequence X f x) := by
    rw [← germSequence_eq]
    exact (SeqKoszul.isH1RegularSequence_iff_forall_germ X r f).mp h x
  exact (isQuasiRegular_ofFn_iff _).mp
    (Koszul.isQuasiRegular_of_isH1RegularOn
      ((Koszul.isH1RegularOn_self_iff (germSequence X f x)).mpr hx))

end Sequences

section IdealSheaves

variable (X : RingedSpace.{u, u}) (J : (structureSheafModule X).Submodule)

/-- **A regular ideal sheaf is Koszul-regular.**  One implication of Stacks tag 063E, between
parts (1) and (2) of Stacks tag 063D. -/
@[stacks 063E "regular implies Koszul-regular"]
theorem isKoszulRegularIdealSheaf_of_isRegularIdealSheaf (h : IsRegularIdealSheaf X J) :
    IsKoszulRegularIdealSheaf X J := by
  intro x hx
  obtain ⟨U, hxU, r, f, hreg, hgen⟩ := h x hx
  exact ⟨U, hxU, r, f, isKoszulSequenceExactOn_of_isRegularSequenceOn X U f hreg, hgen⟩

/-- **An `H₁`-regular ideal sheaf is quasi-regular.**  One implication of Stacks tag 063E, between
parts (3) and (4) of Stacks tag 063D. -/
@[stacks 063E "H₁-regular implies quasi-regular"]
theorem isQuasiRegularIdealSheaf_of_isH1RegularIdealSheaf (h : IsH1RegularIdealSheaf X J) :
    IsQuasiRegularIdealSheaf X J := by
  intro x hx
  obtain ⟨U, hxU, r, f, hh1, hgen⟩ := h x hx
  exact ⟨U, hxU, r, f, isIso_quasiRegularMap_of_isKoszulSequenceExactOn X U f hh1, hgen⟩

end IdealSheaves

section Immersions

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **A regular immersion is Koszul-regular.**  The first implication of Stacks tag 063K, between
parts (1) and (2) of Stacks tag 063J. -/
@[stacks 063K]
theorem isKoszulRegularImmersion_of_isRegularImmersion (h : IsRegularImmersion i) :
    IsKoszulRegularImmersion i :=
  isKoszulRegularIdealSheaf_of_isRegularIdealSheaf
    i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace (definingIdeal i) h

/-- **A Koszul-regular immersion is `H₁`-regular.**  The second implication of Stacks tag 063K,
between parts (2) and (3) of Stacks tag 063J. -/
@[stacks 063K]
theorem isH1RegularImmersion_of_isKoszulRegularImmersion (h : IsKoszulRegularImmersion i) :
    IsH1RegularImmersion i :=
  IsKoszulRegularIdealSheaf.isH1RegularIdealSheaf h

/-- **An `H₁`-regular immersion is quasi-regular.**  The third implication of Stacks tag 063K,
between parts (3) and (4) of Stacks tag 063J. -/
@[stacks 063K]
theorem isQuasiRegularImmersion_of_isH1RegularImmersion (h : IsH1RegularImmersion i) :
    IsQuasiRegularImmersion i :=
  isQuasiRegularIdealSheaf_of_isH1RegularIdealSheaf
    i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace (definingIdeal i) h

end Immersions

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
