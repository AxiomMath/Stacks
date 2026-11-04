module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits

/-!
# Sections of an fppf sheaf over a pushout of the site

Let `S` be a scheme contained in a big fppf site `B`, and let
```
U --g--> W
|        |
f        j
v        v
V --i--> Z
```
be a pushout square of the big fppf site of `S`. For a sheaf `X` on that site this file compares
the sections of `X` over `Z` with the pairs of sections over `V` and `W` agreeing over `U`.

* If every morphism to `X` from a represented sheaf is relatively representable — which is
  Stacks 0AIP for a formal algebraic space — the comparison is injective. The fibre product of
  two sections over `Z` is represented by an object `P` of the site; two sections agreeing over
  `V` and over `W` give compatible maps from `V` and `W` to `P`, hence a section of `P ⟶ Z` by the
  pushout property, along which the two sections are identified.
* If `X` is an affine formal algebraic space and `V`, `W` are affine, the comparison is
  surjective. A section over an affine object factors through a stage of the directed colimit of
  affine schemes presenting `X`; two of them factor through a common stage, compatibly over `U`
  since the colimit injections are monomorphisms, and the two maps into that stage glue along
  the pushout.

These are the two inputs from the target of the Rim–Schlessinger condition (RS) of Stacks 07WP
for a formal algebraic space: injectivity holds for the whole space, and surjectivity is first
proved on the affine formal charts.

## Main results

* `AlgebraicGeometry.FormalSpace.eq_of_isPushout`: injectivity, for a sheaf with representable
  relative products.
* `AlgebraicGeometry.FormalSpace.exists_eq_of_isPushout_of_isAffineFormalAlgebraicSpace`:
  surjectivity, for an affine formal algebraic space and affine middle corners.

## References

* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Sections over a pushout are determined by their restrictions.** Let `X` be a sheaf on the
big fppf site of `S` every morphism to which from a represented sheaf is relatively
representable, for instance a formal algebraic space (Stacks 0AIP). Two sections of `X` over the
terminal corner of a pushout square of the site which agree over both middle corners are equal. -/
theorem eq_of_isPushout {X : FppfSheaf B S hS} (hX : HasRepresentableRelativeProducts B S hS X)
    {U V W Z : BigFppfOver B S hS} {f : U ⟶ V} {g : U ⟶ W} {i : V ⟶ Z} {j : W ⟶ Z}
    (hpo : IsPushout f g i j) {a b : X.obj.obj (op Z)}
    (hi : X.obj.map i.op a = X.obj.map i.op b) (hj : X.obj.map j.op a = X.obj.map j.op b) :
    a = b := by
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  let J := BigFppfOver.topology B S hS
  let Y := Sheaf.sheafifiedYoneda J
  let α : Y.obj Z ⟶ X := (Sheaf.sectionEquiv J).symm a
  let β : Y.obj Z ⟶ X := (Sheaf.sectionEquiv J).symm b
  have hres : ∀ {T : BigFppfOver B S hS} (t : T ⟶ Z), X.obj.map t.op a = X.obj.map t.op b →
      Y.map t ≫ α = Y.map t ≫ β := fun t ht => (Sheaf.sectionEquiv J).injective (by
    rw [Sheaf.sectionEquiv_map_comp, Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, ht])
  obtain ⟨P, snd, fst, hpb⟩ := hX α β
  let fst' : P ⟶ Z := Y.preimage fst
  have hfst' : Y.map fst' = fst := Y.map_preimage fst
  -- the maps from the middle corners to the fibre product
  let lV : V ⟶ P := Y.preimage (hpb.lift (Y.map i) (Y.map i) (hres i hi))
  let lW : W ⟶ P := Y.preimage (hpb.lift (Y.map j) (Y.map j) (hres j hj))
  have hlV₁ : lV ≫ fst' = i := Y.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, hfst', IsPullback.lift_fst])
  have hlV₂ : lV ≫ snd = i := Y.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd])
  have hlW₁ : lW ≫ fst' = j := Y.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, hfst', IsPullback.lift_fst])
  have hlW₂ : lW ≫ snd = j := Y.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd])
  have hcompat : f ≫ lV = g ≫ lW := Y.map_injective (hpb.hom_ext
    (by rw [← hfst', ← Y.map_comp, ← Y.map_comp, Category.assoc, Category.assoc, hlV₁, hlW₁,
      hpo.w])
    (by rw [← Y.map_comp, ← Y.map_comp, Category.assoc, Category.assoc, hlV₂, hlW₂, hpo.w]))
  let s : Z ⟶ P := hpo.desc lV lW hcompat
  have hs₁ : s ≫ fst' = 𝟙 Z := hpo.hom_ext
    (by rw [hpo.inl_desc_assoc, hlV₁, Category.comp_id])
    (by rw [hpo.inr_desc_assoc, hlW₁, Category.comp_id])
  have hs₂ : s ≫ snd = 𝟙 Z := hpo.hom_ext
    (by rw [hpo.inl_desc_assoc, hlV₂, Category.comp_id])
    (by rw [hpo.inr_desc_assoc, hlW₂, Category.comp_id])
  refine (Sheaf.sectionEquiv J).symm.injective ?_
  calc α = Y.map (s ≫ fst') ≫ α := by rw [hs₁, Y.map_id, Category.id_comp]
    _ = Y.map s ≫ fst ≫ α := by rw [Y.map_comp, hfst', Category.assoc]
    _ = Y.map s ≫ Y.map snd ≫ β := by rw [hpb.w]
    _ = β := by rw [← Category.assoc, ← Y.map_comp, hs₂, Y.map_id, Category.id_comp]

/-- **Sections of an affine formal algebraic space glue along a pushout of affine objects.** Let
`X` be an affine formal algebraic space over `S` and let `V ⟵ U ⟶ W` be completed to a pushout
square of the big fppf site of `S` with `V` and `W` affine. Then a section of `X` over `V` and a
section over `W` which agree over `U` are the restrictions of one section over the terminal
corner.

Both sections factor through a common stage of the directed system of affine schemes presenting
`X`, compatibly over `U` because the injections of the colimit are monomorphisms; the two maps
into the stage then glue along the pushout. -/
theorem exists_eq_of_isPushout_of_isAffineFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    {U V W Z : BigFppfOver B S hS} {f : U ⟶ V} {g : U ⟶ W} {i : V ⟶ Z} {j : W ⟶ Z}
    (hpo : IsPushout f g i j) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (a : X.obj.obj (op V))
    (b : X.obj.obj (op W)) (hab : X.obj.map f.op a = X.obj.map g.op b) :
    ∃ z : X.obj.obj (op Z), X.obj.map i.op z = a ∧ X.obj.map j.op z = b := by
  classical
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  let J := BigFppfOver.topology B S hS
  let Y := Sheaf.sheafifiedYoneda J
  obtain ⟨-, I, pre, hne, hdir, D, hD, ⟨e⟩⟩ := hX
  let := pre
  have := hne
  have := hdir
  let E := D ⋙ BigAffineFppf.inclusion B S hS ⋙ Y
  have hmono : ∀ (k l : I) (t : k ⟶ l), Mono (E.map t) := fun k l t =>
    let : Mono (E.map t).hom := mono_of_isRepresentableThickeningULift B S hS
      (isRepresentableThickeningULift_sheafifiedYoneda_map B S hS
        ((BigAffineFppf.inclusion B S hS).map (D.map t)) (hD t))
    Sheaf.Hom.mono_of_presheaf_mono J (Type (u + 1)) (E.map t)
  -- the two sections factor through stages
  obtain ⟨k, α, hα⟩ := compact_map_factors_through_filtered_colimit E hmono V
    (isQuasiCompactObject_over_of_compact_scheme B S hS V)
    ((Sheaf.sectionEquiv J).symm a ≫ e.hom)
  obtain ⟨l, β, hβ⟩ := compact_map_factors_through_filtered_colimit E hmono W
    (isQuasiCompactObject_over_of_compact_scheme B S hS W)
    ((Sheaf.sectionEquiv J).symm b ≫ e.hom)
  obtain ⟨m, hkm, hlm⟩ := directed_of (· ≤ ·) k l
  obtain ⟨α', hα'⟩ : ∃ α' : Y.obj V ⟶ E.obj m,
      α' ≫ colimit.ι E m = (Sheaf.sectionEquiv J).symm a ≫ e.hom :=
    ⟨α ≫ E.map (homOfLE hkm), by rw [Category.assoc, colimit.w, hα]⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : Y.obj W ⟶ E.obj m,
      β' ≫ colimit.ι E m = (Sheaf.sectionEquiv J).symm b ≫ e.hom :=
    ⟨β ≫ E.map (homOfLE hlm), by rw [Category.assoc, colimit.w, hβ]⟩
  have : Mono (colimit.ι E m) := Sheaf.mono_colimit_ι_of_mono_transition E hmono m
  let aV : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj m) := Y.preimage α'
  let bW : W ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj m) := Y.preimage β'
  have hrestr : ∀ {T T' : BigFppfOver B S hS} (t : T ⟶ T') (c : X.obj.obj (op T')),
      (Sheaf.sectionEquiv J).symm (X.obj.map t.op c) = Y.map t ≫ (Sheaf.sectionEquiv J).symm c :=
    fun t c => (Sheaf.sectionEquiv J).symm_apply_eq.2 (by
      rw [Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply])
  have hcompat : f ≫ aV = g ≫ bW := Y.map_injective (by
    rw [Y.map_comp, Y.map_comp, Functor.map_preimage, Functor.map_preimage]
    refine (cancel_mono (colimit.ι E m)).1 ?_
    rw [Category.assoc, Category.assoc, hα', hβ', ← Category.assoc, ← Category.assoc,
      ← hrestr, ← hrestr, hab])
  let s := hpo.desc aV bW hcompat
  refine ⟨Sheaf.sectionEquiv J (Y.map s ≫ colimit.ι E m ≫ e.inv), ?_, ?_⟩
  · rw [← Sheaf.sectionEquiv_map_comp, ← Category.assoc, ← Y.map_comp, hpo.inl_desc,
      Functor.map_preimage, ← Category.assoc, hα', Category.assoc, e.hom_inv_id,
      Category.comp_id, Equiv.apply_symm_apply]
  · rw [← Sheaf.sectionEquiv_map_comp, ← Category.assoc, ← Y.map_comp, hpo.inr_desc,
      Functor.map_preimage, ← Category.assoc, hβ', Category.assoc, e.hom_inv_id,
      Category.comp_id, Equiv.apply_symm_apply]

end AlgebraicGeometry.FormalSpace
