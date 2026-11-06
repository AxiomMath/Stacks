module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.AlgebraicGeometry.Pushout.CartesianTriple
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent

/-!
# Flat and étale descent across a pushout along a closed immersion and an integral morphism

Let `Y ← Z → X` be the span of a pushout situation of [Stacks Project, Tag 0ECI], so that the
pushout `Y ⨿_Z X` exists.  This file proves [Stacks Project, Tag 0ECL]: the category of schemes
which are flat, separated and locally quasi-finite over `Y ⨿_Z X` is equivalent to the category
of cartesian triples `Y' ← Z' → X'` over the span, as in [Stacks Project, Tag 0ECK], whose three
vertical morphisms are flat; and the same with "flat" replaced by "étale".

The functor is the pushout construction of Tag 0ECK, which is fully faithful already at the
level of cartesian triples.  What is proved here is that it lands in the asserted subcategory —
the induced morphism of pushouts is flat, respectively étale — and that it is essentially
surjective: every flat, separated, locally quasi-finite scheme over `Y ⨿_Z X` is the pushout of
its two base changes to `X` and to `Y`.

## Main results

* `AlgebraicGeometry.flat_pushoutMap` and `AlgebraicGeometry.etale_pushoutMap`: the induced
  morphism of pushouts inherits flatness, respectively étaleness, from the three vertical
  morphisms.
* `AlgebraicGeometry.isIso_pushoutBaseChangeMap`: a flat, separated, locally quasi-finite
  scheme over the pushout is the pushout of its two base changes.
* `AlgebraicGeometry.flatTriple_pushout_equivalence` and
  `AlgebraicGeometry.etaleTriple_pushout_equivalence`: the two asserted equivalences, together
  with the identification of the functor with the canonical pushout construction on objects and
  on the two constituents.

## Implementation notes

Both properties of the induced morphism are read off from one affine computation, carried out
for an arbitrary property of ring maps which is closed under composition, holds for bijections,
and is compatible with the gluing of algebras over a ring fibre product of
[Stacks Project, Tag 08KQ]; flatness and étaleness are the two instances used.

Essential surjectivity rests on the comparison morphism from the pushout of the two base changes.
It is surjective and universally closed because the two canonical morphisms into a pushout are
jointly surjective and universally closed, hence finite — so affine — by Zariski's main theorem,
and an affine morphism is an isomorphism as soon as it is one on sections over an affine cover.
That last check is where flatness is used: over affine charts it becomes the statement that a
map of flat algebras over a ring fibre product with isomorphic base changes is an isomorphism.

Stacks terminology includes local finite type in "locally quasi-finite".  Mathlib separates this
into `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`, so both
conditions appear in the categories of schemes over the pushout and in the data of a cartesian
triple.

## References

* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECK](https://stacks.math.columbia.edu/tag/0ECK)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The common core of flatness and étaleness of the induced morphism of pushouts.  Let `P` be a
property of ring maps which holds for bijections, is stable under composition, and is stable
under the gluing of [Stacks Project, Tag 08KQ] — that is, passes from two algebras over the two
factors of a ring fibre product to the induced algebra over the fibre product.  If `P` holds for
the maps on sections of the two outer vertical morphisms of a cartesian triple, then it holds
for the maps on sections of the induced morphism of pushouts.

Over an affine open `U` of `Y ⨿_Z X` and an affine open `V` of `Y' ⨿_{Z'} X'` above it, the
sections of either pushout form a fibre product of rings by [Stacks Project, Tag 0E25], the two
squares of the triple give pushout squares of sections by
`AlgebraicGeometry.isPushout_appLE_of_isPullback`, and the map on sections induced by the
morphism of pushouts is the canonical comparison map of Milnor patching up to the two
identifications. -/
private theorem appLE_pushoutMap_of_ringHomProperty
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hbij : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S),
      Function.Bijective f → P f)
    (hcomp : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
      (f : R →+* S) (g : S →+* T), P f → P g → P (g.comp f))
    (hglue : ∀ {A A' B D C' C : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D]
      [CommRing C'] [CommRing C] (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
      (base : RingFibreProduct.Situation toBase surjection I) (BtoD : B →+* D)
      (A'toC' : A' →+* C') (AtoC : A →+* C) (DtoC : D →+* C) (C'toC : C' →+* C),
      MilnorPatching.ringPushout BtoD toBase DtoC AtoC →
      MilnorPatching.ringPushout A'toC' surjection C'toC AtoC →
      ∀ (hcompat : ∀ x : base.fibreProduct,
          DtoC (BtoD (base.pullbackCone.fst.hom x)) =
            C'toC (A'toC' (base.pullbackCone.snd.hom x))),
        P BtoD → P A'toC' →
        P (RingHom.codRestrict ((BtoD.comp base.pullbackCone.fst.hom).prod
          (A'toC'.comp base.pullbackCone.snd.hom)) (RingHom.pullback DtoC C'toC) hcompat))
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s)
    (hPf : ∀ (U : s.X.Opens), IsAffineOpen U → ∀ (V : d.X'.Opens), IsAffineOpen V →
      ∀ e : V ≤ d.f ⁻¹ᵁ U, P (d.f.appLE U V e).hom)
    (hPg : ∀ (U : s.Y.Opens), IsAffineOpen U → ∀ (V : d.Y'.Opens), IsAffineOpen V →
      ∀ e : V ≤ d.g ⁻¹ᵁ U, P (d.g.appLE U V e).hom)
    {U : (pushoutScheme s).Opens} (hU : IsAffineOpen U)
    {V : (pushoutScheme (inducedSituation s d)).Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ pushoutMap s d ⁻¹ᵁ U) :
    P ((pushoutMap s d).appLE U V hVU).hom := by
  let s' := inducedSituation s d
  let UX : s.X.Opens := pushoutInl s ⁻¹ᵁ U
  let UY : s.Y.Opens := pushoutInr s ⁻¹ᵁ U
  let UZ : s.Z.Opens := s.j ⁻¹ᵁ UY
  let VX : d.X'.Opens := pushoutInl s' ⁻¹ᵁ V
  let VY : d.Y'.Opens := pushoutInr s' ⁻¹ᵁ V
  let VZ : d.Z'.Opens := d.j' ⁻¹ᵁ VY
  have hUX : IsAffineOpen UX := hU.preimage (pushoutInl s)
  have hUY : IsAffineOpen UY := hU.preimage (pushoutInr s)
  have hUZ : IsAffineOpen UZ := hUY.preimage s.j
  have hVX : IsAffineOpen VX := hV.preimage (pushoutInl s')
  have hVY : IsAffineOpen VY := hV.preimage (pushoutInr s')
  have hj' : IsIntegralHom d.j' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback d.right_isPullback.flip inferInstance
  have hVZ : IsAffineOpen VZ := hVY.preimage d.j'
  have eU : s.i ⁻¹ᵁ UX = s.j ⁻¹ᵁ UY :=
    congrArg (fun k : s.Z ⟶ pushoutScheme s ↦ k ⁻¹ᵁ U)
      (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
  let toBase : Γ(s.Y, UY) →+* Γ(s.Z, UZ) := (s.j.appLE UY UZ le_rfl).hom
  let surjection : Γ(s.X, UX) →+* Γ(s.Z, UZ) := (s.i.appLE UX UZ eU.symm.le).hom
  have hsurj : Function.Surjective surjection := by
    have hcan : Function.Surjective (s.i.appLE UX (s.i ⁻¹ᵁ UX) le_rfl).hom := by
      simpa only [Scheme.Hom.appLE_eq_app] using s.i.app_surjective UX hUX
    exact (s.i.appLE_congr eU.symm.le rfl eU.symm
      (fun f => Function.Surjective f.hom)).mpr hcan
  let base : RingFibreProduct.Situation toBase surjection (RingHom.ker surjection) :=
    ⟨hsurj, rfl⟩
  have hle : ∀ {A B : Scheme.{u}} (a : A ⟶ pushoutScheme s') (a₀ : B ⟶ pushoutScheme s)
      (φ : A ⟶ B), a ≫ pushoutMap s d = φ ≫ a₀ → a ⁻¹ᵁ V ≤ φ ⁻¹ᵁ (a₀ ⁻¹ᵁ U) := by
    intro A B a a₀ φ hw x hx
    have hq : pushoutMap s d (a x) ∈ U := hVU hx
    change (a ≫ pushoutMap s d) x ∈ U at hq
    rwa [hw] at hq
  have hVYg : VY ≤ d.g ⁻¹ᵁ UY := hle _ _ _ (pushoutMap_right_isPullback s d).w
  have hVZh : VZ ≤ d.h ⁻¹ᵁ UZ := by
    intro z hz
    have hy : d.g (d.j' z) ∈ UY := hVYg hz
    have hw : d.g (d.j' z) = s.j (d.h z) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun k : d.Z' ⟶ s.Y ↦ k z) d.right_isPullback.w
    show s.j (d.h z) ∈ UY
    rw [← hw]
    exact hy
  have hVXi : VX ≤ d.f ⁻¹ᵁ UX := hle _ _ _ (pushoutMap_left_isPullback s d).w
  have eV : d.i' ⁻¹ᵁ VX = d.j' ⁻¹ᵁ VY :=
    congrArg (fun k : d.Z' ⟶ pushoutScheme s' ↦ k ⁻¹ᵁ V)
      (pushoutAlongClosedImmersionAndIntegral s').isPushout.w
  have hVZi : VZ ≤ d.i' ⁻¹ᵁ VX := le_of_eq eV.symm
  let BtoD : Γ(s.Y, UY) →+* Γ(d.Y', VY) := (d.g.appLE UY VY hVYg).hom
  let DtoC : Γ(d.Y', VY) →+* Γ(d.Z', VZ) := (d.j'.appLE VY VZ le_rfl).hom
  let AtoC : Γ(s.Z, UZ) →+* Γ(d.Z', VZ) := (d.h.appLE UZ VZ hVZh).hom
  have hUW_D : VZ = d.h ⁻¹ᵁ UZ ⊓ d.j' ⁻¹ᵁ VY :=
    le_antisymm (le_inf hVZh le_rfl) inf_le_right
  have hUW_C : VZ = d.h ⁻¹ᵁ UZ ⊓ d.i' ⁻¹ᵁ VX :=
    le_antisymm (le_inf hVZh hVZi) (inf_le_right.trans (le_of_eq eV))
  have hD : MilnorPatching.ringPushout BtoD toBase DtoC AtoC :=
    MilnorPatching.ringPushout_of_isPushout _ _ _ _
      (isPushout_appLE_of_isPullback d.right_isPullback.flip hUY hUZ (by rfl) hVY hVYg
        hUW_D).flip
  let A'toC' : Γ(s.X, UX) →+* Γ(d.X', VX) := (d.f.appLE UX VX hVXi).hom
  let C'toC : Γ(d.X', VX) →+* Γ(d.Z', VZ) := (d.i'.appLE VX VZ hVZi).hom
  have hC' : MilnorPatching.ringPushout A'toC' surjection C'toC AtoC :=
    MilnorPatching.ringPushout_of_isPushout _ _ _ _
      (isPushout_appLE_of_isPullback d.left_isPullback.flip hUX hUZ eU.symm.le hVX hVXi
        hUW_C).flip
  have hUΓ : IsPullback (pushoutInr s |>.app U) (pushoutInl s |>.app U)
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection) := by
    convert pushoutStructureSheaf_isPullback s U using 1
    · exact Scheme.Hom.appLE_eq_app s.j
    · show s.i.appLE UX UZ eU.symm.le =
        s.i.app UX ≫ eqToHom (congrArg (fun W ↦ Γ(s.Z, W)) eU)
      show s.i.app UX ≫ s.Z.presheaf.map (homOfLE eU.symm.le).op =
        s.i.app UX ≫ eqToHom (congrArg (fun W ↦ Γ(s.Z, W)) eU)
      rw [← eqToHom_map s.Z.presheaf (congrArg (fun W : s.Z.Opens ↦ Opposite.op W) eU)]
      congr 1
  have hVΓ : IsPullback (pushoutInr s' |>.app V) (pushoutInl s' |>.app V)
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom C'toC) := by
    convert pushoutStructureSheaf_isPullback s' V using 1
    · exact Scheme.Hom.appLE_eq_app d.j'
    · show d.i'.appLE VX VZ hVZi =
        d.i'.app VX ≫ eqToHom (congrArg (fun W ↦ Γ(d.Z', W)) eV)
      show d.i'.app VX ≫ d.Z'.presheaf.map (homOfLE hVZi).op =
        d.i'.app VX ≫ eqToHom (congrArg (fun W ↦ Γ(d.Z', W)) eV)
      rw [← eqToHom_map d.Z'.presheaf (congrArg (fun W : d.Z'.Opens ↦ Opposite.op W) eV)]
      congr 1
  have hBaseCanon : IsPullback base.pullbackCone.fst base.pullbackCone.snd
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection) :=
    IsPullback.of_isLimit base.pullbackConeIsLimit
  let eBase := hUΓ.isoIsPullback (CommRingCat.of Γ(s.Y, UY))
    (CommRingCat.of Γ(s.X, UX)) hBaseCanon
  let cTarget := CommRingCat.pullbackCone (CommRingCat.ofHom DtoC) (CommRingCat.ofHom C'toC)
  have hTargetCanon : IsPullback cTarget.fst cTarget.snd
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom C'toC) :=
    IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom C'toC))
  let eTarget := hVΓ.isoIsPullback (CommRingCat.of Γ(d.Y', VY))
    (CommRingCat.of Γ(d.X', VX)) hTargetCanon
  have hBaseFst : eBase.hom ≫ base.pullbackCone.fst = (pushoutInr s).app U := by
    simpa only [eBase] using IsPullback.isoIsPullback_hom_fst
      (CommRingCat.of Γ(s.Y, UY)) (CommRingCat.of Γ(s.X, UX)) hUΓ hBaseCanon
  have hBaseSnd : eBase.hom ≫ base.pullbackCone.snd = (pushoutInl s).app U := by
    simpa only [eBase] using IsPullback.isoIsPullback_hom_snd
      (CommRingCat.of Γ(s.Y, UY)) (CommRingCat.of Γ(s.X, UX)) hUΓ hBaseCanon
  have hTargetFst : eTarget.hom ≫ cTarget.fst = (pushoutInr s').app V := by
    simpa only [eTarget] using IsPullback.isoIsPullback_hom_fst
      (CommRingCat.of Γ(d.Y', VY)) (CommRingCat.of Γ(d.X', VX)) hVΓ hTargetCanon
  have hTargetSnd : eTarget.hom ≫ cTarget.snd = (pushoutInl s').app V := by
    simpa only [eTarget] using IsPullback.isoIsPullback_hom_snd
      (CommRingCat.of Γ(d.Y', VY)) (CommRingCat.of Γ(d.X', VX)) hVΓ hTargetCanon
  let toB : base.fibreProduct →+* Γ(s.Y, UY) := base.pullbackCone.fst.hom
  let toA' : base.fibreProduct →+* Γ(s.X, UX) := base.pullbackCone.snd.hom
  have hcompat : ∀ x : base.fibreProduct, DtoC (BtoD (toB x)) = C'toC (A'toC' (toA' x)) := by
    intro x
    have hd : DtoC.comp BtoD = AtoC.comp toBase := MilnorPatching.ringPushout_comm hD
    have hc : C'toC.comp A'toC' = AtoC.comp surjection := MilnorPatching.ringPushout_comm hC'
    calc
      _ = AtoC (toBase (toB x)) := DFunLike.congr_fun hd (toB x)
      _ = AtoC (surjection (toA' x)) := congrArg AtoC
        (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
      _ = _ := (DFunLike.congr_fun hc (toA' x)).symm
  let toD' : base.fibreProduct →+* RingHom.pullback DtoC C'toC :=
    RingHom.codRestrict ((BtoD.comp toB).prod (A'toC'.comp toA'))
      (RingHom.pullback DtoC C'toC) hcompat
  have hsourceObj : base.pullbackCone.pt = CommRingCat.of base.fibreProduct := rfl
  let toD'cat : base.pullbackCone.pt ⟶ cTarget.pt :=
    eqToHom hsourceObj ≫ CommRingCat.ofHom toD'
  have hproj₁ : toD'cat ≫ cTarget.fst =
      base.pullbackCone.fst ≫ CommRingCat.ofHom BtoD := by
    ext x
    rfl
  have hproj₂ : toD'cat ≫ cTarget.snd =
      base.pullbackCone.snd ≫ CommRingCat.ofHom A'toC' := by
    ext x
    rfl
  let chartMap := (pushoutMap s d).appLE U V hVU
  have hApp : ∀ {A B : Scheme.{u}} (a : A ⟶ pushoutScheme s') (a₀ : B ⟶ pushoutScheme s)
      (φ : A ⟶ B) (hw : a ≫ pushoutMap s d = φ ≫ a₀),
      chartMap ≫ a.app V = a₀.app U ≫ φ.appLE (a₀ ⁻¹ᵁ U) (a ⁻¹ᵁ V) (hle a a₀ φ hw) := by
    intro A B a a₀ φ hw
    have hcomp : a ⁻¹ᵁ V ≤ (φ ≫ a₀) ⁻¹ᵁ U := by
      simpa only [Scheme.Hom.comp_preimage] using hle a a₀ φ hw
    calc
      chartMap ≫ a.app V = (a ≫ pushoutMap s d).appLE U (a ⁻¹ᵁ V) _ := by
            simpa only [chartMap, Scheme.Hom.app_eq_appLE] using
              (Scheme.Hom.appLE_comp_appLE a (pushoutMap s d) U V (a ⁻¹ᵁ V) hVU le_rfl)
      _ = (φ ≫ a₀).appLE U (a ⁻¹ᵁ V) hcomp := Scheme.Hom.appLE_congr_hom hw U _ _ hcomp
      _ = _ := Scheme.Hom.comp_appLE φ a₀ U _ hcomp
  have hInr := hApp _ _ _ (pushoutMap_right_isPullback s d).w
  have hInl := hApp _ _ _ (pushoutMap_left_isPullback s d).w
  have hmap : eBase.hom ≫ toD'cat = chartMap ≫ eTarget.hom := by
    apply hTargetCanon.hom_ext
    · calc
        eBase.hom ≫ toD'cat ≫ cTarget.fst =
            eBase.hom ≫ base.pullbackCone.fst ≫ CommRingCat.ofHom BtoD := by rw [hproj₁]
        _ = (pushoutInr s).app U ≫ d.g.appLE UY VY hVYg := by
              rw [← Category.assoc, hBaseFst]
              rfl
        _ = chartMap ≫ (pushoutInr s').app V := hInr.symm
        _ = chartMap ≫ eTarget.hom ≫ cTarget.fst := by rw [hTargetFst]
    · calc
        eBase.hom ≫ toD'cat ≫ cTarget.snd =
            eBase.hom ≫ base.pullbackCone.snd ≫ CommRingCat.ofHom A'toC' := by rw [hproj₂]
        _ = (pushoutInl s).app U ≫ d.f.appLE UX VX hVXi := by
              rw [← Category.assoc, hBaseSnd]
              rfl
        _ = chartMap ≫ (pushoutInl s').app V := hInl.symm
        _ = chartMap ≫ eTarget.hom ≫ cTarget.snd := by rw [hTargetSnd]
  have hB : P BtoD := hPg UY hUY VY hVY hVYg
  have hA' : P A'toC' := hPf UX hUX VX hVX hVXi
  have htoD' : P toD' :=
    hglue toBase surjection (RingHom.ker surjection) base BtoD A'toC' AtoC DtoC C'toC
      hD hC' hcompat hB hA'
  have hBaseP : P eBase.hom.hom :=
    hbij _ ((ConcreteCategory.isIso_iff_bijective eBase.hom).mp inferInstance)
  have hTargetP : P eTarget.inv.hom :=
    hbij _ ((ConcreteCategory.isIso_iff_bijective eTarget.inv).mp inferInstance)
  have hsourceP : P (eqToHom hsourceObj).hom :=
    hbij _ ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)
  have htoD'cat : P toD'cat.hom := hcomp _ _ hsourceP htoD'
  have hfactor : chartMap = eBase.hom ≫ toD'cat ≫ eTarget.inv := by
    rw [← Category.assoc, hmap]
    simp
  rw [show chartMap.hom = (eBase.hom ≫ toD'cat ≫ eTarget.inv).hom from
    congrArg CommRingCat.Hom.hom hfactor]
  simpa only [CommRingCat.hom_comp, RingHom.comp_assoc] using
    hcomp _ _ (hcomp _ _ hBaseP htoD'cat) hTargetP

/-- **Stacks Project, Tag 0ECL.** The morphism of pushouts induced by a cartesian triple whose
three vertical morphisms are flat is flat. -/
@[stacks 0ECL "flatness of the pushout map"]
theorem flat_pushoutMap (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (d : CartesianDiagram s) [Flat d.f] [Flat d.g] [Flat d.h] :
    Flat (pushoutMap s d) := by
  rw [flat_iff]
  intro U hU V hV hVU
  exact appLE_pushoutMap_of_ringHomProperty (P := fun f ↦ f.Flat)
    (fun _ hf ↦ RingHom.Flat.of_bijective hf)
    (fun _ _ hf hg ↦ RingHom.Flat.comp hf hg)
    (fun toBase surjection I base BtoD A'toC' AtoC DtoC C'toC hD hC' _ hB hA' ↦
      MilnorPatching.flat_pullbackMap_of_ringPushout toBase surjection I base
        BtoD A'toC' AtoC DtoC C'toC hD hC' hB hA')
    s d (fun _ hU _ hV e ↦ Flat.flat_appLE d.f hU hV e)
    (fun _ hU _ hV e ↦ Flat.flat_appLE d.g hU hV e) hU hV hVU

/-- **Stacks Project, Tag 0ECL.** The morphism of pushouts induced by a cartesian triple whose
three vertical morphisms are étale is étale. -/
@[stacks 0ECL "étaleness of the pushout map"]
theorem etale_pushoutMap (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (d : CartesianDiagram s) [Etale d.f] [Etale d.g] [Etale d.h] :
    Etale (pushoutMap s d) := by
  rw [etale_iff]
  intro U hU V hV hVU
  exact appLE_pushoutMap_of_ringHomProperty (P := fun f ↦ f.Etale)
    (fun _ hf ↦ RingHom.Etale.of_bijective hf)
    (fun f g hf hg ↦ RingHom.Etale.stableUnderComposition f g hf hg)
    (fun toBase surjection I base BtoD A'toC' AtoC DtoC C'toC hD hC' _ hB hA' ↦
      MilnorPatching.etale_pullbackMap_of_ringPushout toBase surjection I base
        BtoD A'toC' AtoC DtoC C'toC hD hC' hB hA')
    s d (fun _ hU _ hV e ↦ Etale.etale_appLE d.f hU hV e)
    (fun _ hU _ hV e ↦ Etale.etale_appLE d.g hU hV e) hU hV hVU

/-- The pushout construction as a functor from the cartesian triples with flat vertical
morphisms to the flat, separated, locally quasi-finite schemes over the pushout. -/
noncomputable def flatTripleToSchemesOver
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    FlatCartesianTriple s ⥤ flatSchemesOver s :=
  (flatSchemesOverProperty s).lift (flatTripleToOver s) (fun d ↦ by
    have : Flat d.1.f := d.2.1
    have : Flat d.1.g := d.2.2.1
    have : Flat d.1.h := d.2.2.2
    change Flat (pushoutMap s d.1) ∧ IsSeparated (pushoutMap s d.1) ∧
      LocallyOfFiniteType (pushoutMap s d.1) ∧ LocallyQuasiFinite (pushoutMap s d.1)
    exact ⟨flat_pushoutMap s d.1, inferInstance, inferInstance, inferInstance⟩)

/-- The pushout construction as a functor from the cartesian triples with étale vertical
morphisms to the étale, separated, locally quasi-finite schemes over the pushout. -/
noncomputable def etaleTripleToSchemesOver
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    EtaleCartesianTriple s ⥤ etaleSchemesOver s :=
  (etaleSchemesOverProperty s).lift (etaleTripleToOver s) (fun d ↦ by
    have : Etale d.1.f := d.2.1
    have : Etale d.1.g := d.2.2.1
    have : Etale d.1.h := d.2.2.2
    change Etale (pushoutMap s d.1) ∧ IsSeparated (pushoutMap s d.1) ∧
      LocallyOfFiniteType (pushoutMap s d.1) ∧ LocallyQuasiFinite (pushoutMap s d.1)
    exact ⟨etale_pushoutMap s d.1, inferInstance, inferInstance, inferInstance⟩)

/-- The pushout functor on flat cartesian triples is faithful. -/
instance flatTripleToSchemesOver_faithful
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (flatTripleToSchemesOver s).Faithful where
  map_injective {d e} f g h := by
    apply triplePushoutMap_injective
    have hOver := congrArg ((flatSchemesOverProperty s).ι.map) h
    change (flatTripleToOver s).map f = (flatTripleToOver s).map g at hOver
    exact congrArg (fun q ↦ q.left) hOver

/-- The pushout functor on flat cartesian triples is full. -/
instance flatTripleToSchemesOver_full
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (flatTripleToSchemesOver s).Full where
  map_surjective {d e} f := by
    obtain ⟨m, hm⟩ :=
      exists_cartesianTripleHom_of_comp_pushoutMap d.1 e.1 f.hom.left f.hom.w
    refine ⟨m, ?_⟩
    apply (flatSchemesOverProperty s).hom_ext
    apply Over.OverMorphism.ext
    exact hm

/-- The pushout functor on étale cartesian triples is faithful. -/
instance etaleTripleToSchemesOver_faithful
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (etaleTripleToSchemesOver s).Faithful where
  map_injective {d e} f g h := by
    apply triplePushoutMap_injective
    have hOver := congrArg ((etaleSchemesOverProperty s).ι.map) h
    change (etaleTripleToOver s).map f = (etaleTripleToOver s).map g at hOver
    exact congrArg (fun q ↦ q.left) hOver

/-- The pushout functor on étale cartesian triples is full. -/
instance etaleTripleToSchemesOver_full
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (etaleTripleToSchemesOver s).Full where
  map_surjective {d e} f := by
    obtain ⟨m, hm⟩ :=
      exists_cartesianTripleHom_of_comp_pushoutMap d.1 e.1 f.hom.left f.hom.w
    refine ⟨m, ?_⟩
    apply (etaleSchemesOverProperty s).hom_ext
    apply Over.OverMorphism.ext
    exact hm

/-- The cartesian triple obtained by base change of a flat, separated, locally quasi-finite
scheme over the pushout along the two canonical morphisms `X ⟶ Y ⨿_Z X` and `Y ⟶ Y ⨿_Z X`. -/
noncomputable def pushoutBaseChangeDiagram
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) : CartesianDiagram s := by
  letI : Flat w.hom := hw.1
  letI : IsSeparated w.hom := hw.2.1
  letI : LocallyOfFiniteType w.hom := hw.2.2.1
  letI : LocallyQuasiFinite w.hom := hw.2.2.2
  have hcom : s.i ≫ pushoutInl s = s.j ≫ pushoutInr s :=
    (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
  let e1 := pullbackLeftPullbackSndIso w.hom (pushoutInl s) s.i
  let e2 := pullback.congrHom (X := w.left) (Y := s.Z) (Z := pushoutScheme s)
    (f₁ := w.hom) (f₂ := w.hom) (g₁ := s.i ≫ pushoutInl s)
    (g₂ := s.j ≫ pushoutInr s) rfl hcom
  let e3 := pullbackLeftPullbackSndIso w.hom (pushoutInr s) s.j
  let e := e1 ≪≫ e2 ≪≫ e3.symm
  let h' : pullback (pullback.snd w.hom (pushoutInl s)) s.i ⟶ s.Z :=
    pullback.snd (pullback.snd w.hom (pushoutInl s)) s.i
  have h1 : e1.hom ≫ pullback.snd w.hom (s.i ≫ pushoutInl s) = h' :=
    pullbackLeftPullbackSndIso_hom_snd _ _ _
  have h2 : e2.hom ≫ pullback.snd w.hom (s.j ≫ pushoutInr s) =
      pullback.snd w.hom (s.i ≫ pushoutInl s) := by
    change pullback.map w.hom (s.i ≫ pushoutInl s) w.hom
      (s.j ≫ pushoutInr s) (𝟙 w.left) (𝟙 s.Z) (𝟙 (pushoutScheme s))
      (by simp) (by simpa using hcom) ≫ pullback.snd w.hom (s.j ≫ pushoutInr s) =
      pullback.snd w.hom (s.i ≫ pushoutInl s)
    rw [pullback.map, pullback.lift_snd]
    simp
  have h3 : e3.symm.hom ≫ pullback.snd (pullback.snd w.hom (pushoutInr s)) s.j =
      pullback.snd w.hom (s.j ≫ pushoutInr s) := by
    apply (cancel_epi e3.hom).1
    calc
      e3.hom ≫ e3.symm.hom ≫ pullback.snd (pullback.snd w.hom (pushoutInr s)) s.j =
          (e3.hom ≫ e3.symm.hom) ≫
            pullback.snd (pullback.snd w.hom (pushoutInr s)) s.j :=
            (Category.assoc _ _ _).symm
      _ = pullback.snd (pullback.snd w.hom (pushoutInr s)) s.j := by simp
      _ = e3.hom ≫ pullback.snd w.hom (s.j ≫ pushoutInr s) :=
            (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm
  have hesnd : e.hom ≫ pullback.snd (pullback.snd w.hom (pushoutInr s)) s.j = h' := by
    calc
      e.hom ≫ pullback.snd (pullback.snd w.hom (pushoutInr s)) s.j =
          (e1.hom ≫ e2.hom) ≫
            e3.symm.hom ≫ pullback.snd (pullback.snd w.hom (pushoutInr s)) s.j := by
            simp [e, Category.assoc]
      _ = (e1.hom ≫ e2.hom) ≫ pullback.snd w.hom (s.j ≫ pushoutInr s) := by rw [h3]
      _ = e1.hom ≫ e2.hom ≫ pullback.snd w.hom (s.j ≫ pushoutInr s) := Category.assoc _ _ _
      _ = e1.hom ≫ pullback.snd w.hom (s.i ≫ pushoutInl s) := by rw [h2]
      _ = h' := h1
  refine {
    X' := pullback w.hom (pushoutInl s)
    Y' := pullback w.hom (pushoutInr s)
    Z' := pullback (pullback.snd w.hom (pushoutInl s)) s.i
    i' := pullback.fst (pullback.snd w.hom (pushoutInl s)) s.i
    j' := e.hom ≫ pullback.fst (pullback.snd w.hom (pushoutInr s)) s.j
    f := pullback.snd w.hom (pushoutInl s)
    g := pullback.snd w.hom (pushoutInr s)
    h := h'
    left_isPullback := IsPullback.of_hasPullback _ _
    right_isPullback := ?_ }
  refine IsPullback.of_iso (IsPullback.of_hasPullback
    (pullback.snd w.hom (pushoutInr s)) s.j) e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · change pullback.fst (pullback.snd w.hom (pushoutInr s)) s.j ≫ 𝟙 _ =
      e.symm.hom ≫ e.hom ≫ pullback.fst (pullback.snd w.hom (pushoutInr s)) s.j
    simp
  · change pullback.snd (pullback.snd w.hom (pushoutInr s)) s.j ≫ 𝟙 _ = e.symm.hom ≫ h'
    rw [← hesnd]
    simp
  · simp
  · simp

/-- The morphism from the pushout of the base change triple to the original scheme over the
pushout, from the universal property of the pushout. -/
noncomputable def pushoutBaseChangeMap
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    pushoutScheme (inducedSituation s (pushoutBaseChangeDiagram s w hw)) ⟶ w.left := by
  refine (pushoutAlongClosedImmersionAndIntegral
    (inducedSituation s (pushoutBaseChangeDiagram s w hw))).isPushout.desc
    (pullback.fst w.hom (pushoutInl s)) (pullback.fst w.hom (pushoutInr s)) ?_
  dsimp [pushoutBaseChangeDiagram]
  let e1 := pullbackLeftPullbackSndIso w.hom (pushoutInl s) s.i
  let e2 := pullback.congrHom (X := w.left) (Y := s.Z) (Z := pushoutScheme s)
    (f₁ := w.hom) (f₂ := w.hom) (g₁ := s.i ≫ pushoutInl s)
    (g₂ := s.j ≫ pushoutInr s) rfl (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
  let e3 := pullbackLeftPullbackSndIso w.hom (pushoutInr s) s.j
  have hf2 : e2.hom ≫ pullback.fst w.hom (s.j ≫ pushoutInr s) =
      pullback.fst w.hom (s.i ≫ pushoutInl s) := by
    change pullback.map w.hom (s.i ≫ pushoutInl s) w.hom
      (s.j ≫ pushoutInr s) (𝟙 w.left) (𝟙 s.Z) (𝟙 (pushoutScheme s))
      (by simp) (by simpa using (pushoutAlongClosedImmersionAndIntegral s).isPushout.w) ≫
      pullback.fst w.hom (s.j ≫ pushoutInr s) = pullback.fst w.hom (s.i ≫ pushoutInl s)
    rw [pullback.map, pullback.lift_fst]
    simp
  have hf3 : e3.symm.hom ≫ pullback.fst (pullback.snd w.hom (pushoutInr s)) s.j ≫
      pullback.fst w.hom (pushoutInr s) = pullback.fst w.hom (s.j ≫ pushoutInr s) := by
    apply (cancel_epi e3.hom).1
    calc
      e3.hom ≫ e3.symm.hom ≫ pullback.fst (pullback.snd w.hom (pushoutInr s)) s.j ≫
          pullback.fst w.hom (pushoutInr s) =
          (e3.hom ≫ e3.symm.hom) ≫
            pullback.fst (pullback.snd w.hom (pushoutInr s)) s.j ≫
              pullback.fst w.hom (pushoutInr s) := by simp
      _ = pullback.fst (pullback.snd w.hom (pushoutInr s)) s.j ≫
          pullback.fst w.hom (pushoutInr s) := by simp
      _ = e3.hom ≫ pullback.fst w.hom (s.j ≫ pushoutInr s) :=
        (pullbackLeftPullbackSndIso_hom_fst _ _ _).symm
  calc
    _ = e1.hom ≫ pullback.fst w.hom (s.i ≫ pushoutInl s) :=
      (pullbackLeftPullbackSndIso_hom_fst _ _ _).symm
    _ = e1.hom ≫ e2.hom ≫ pullback.fst w.hom (s.j ≫ pushoutInr s) :=
      congrArg (fun k ↦ e1.hom ≫ k) hf2.symm
    _ = (e1.hom ≫ e2.hom) ≫ pullback.fst w.hom (s.j ≫ pushoutInr s) :=
      (Category.assoc _ _ _).symm
    _ = e1.hom ≫ e2.hom ≫ e3.symm.hom ≫
        pullback.fst (pullback.snd w.hom (pushoutInr s)) s.j ≫
          pullback.fst w.hom (pushoutInr s) := by rw [hf3, Category.assoc]

/-- The comparison morphism restricts on the `X`-part to the base change of `w` along
`X ⟶ Y ⨿_Z X`. -/
theorem pushoutInl_comp_pushoutBaseChangeMap
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    pushoutInl (inducedSituation s (pushoutBaseChangeDiagram s w hw)) ≫
        pushoutBaseChangeMap s w hw =
      pullback.fst w.hom (pushoutInl s) := by
  dsimp [pushoutBaseChangeMap]
  exact (pushoutAlongClosedImmersionAndIntegral
    (inducedSituation s (pushoutBaseChangeDiagram s w hw))).isPushout.inl_desc _ _ _

/-- The comparison morphism restricts on the `Y`-part to the base change of `w` along
`Y ⟶ Y ⨿_Z X`. -/
theorem pushoutInr_comp_pushoutBaseChangeMap
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    pushoutInr (inducedSituation s (pushoutBaseChangeDiagram s w hw)) ≫
        pushoutBaseChangeMap s w hw =
      pullback.fst w.hom (pushoutInr s) := by
  dsimp [pushoutBaseChangeMap]
  exact (pushoutAlongClosedImmersionAndIntegral
    (inducedSituation s (pushoutBaseChangeDiagram s w hw))).isPushout.inr_desc _ _ _

/-- The comparison morphism is a morphism over the pushout. -/
theorem pushoutBaseChangeMap_comp_hom
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    pushoutBaseChangeMap s w hw ≫ w.hom = pushoutMap s (pushoutBaseChangeDiagram s w hw) := by
  apply (pushoutAlongClosedImmersionAndIntegral
    (inducedSituation s (pushoutBaseChangeDiagram s w hw))).isPushout.hom_ext
  · rw [← Category.assoc, pushoutInl_comp_pushoutBaseChangeMap,
      (pushoutMap_left_isPullback s (pushoutBaseChangeDiagram s w hw)).w]
    dsimp [pushoutBaseChangeDiagram]
    exact pullback.condition
  · rw [← Category.assoc, pushoutInr_comp_pushoutBaseChangeMap,
      (pushoutMap_right_isPullback s (pushoutBaseChangeDiagram s w hw)).w]
    dsimp [pushoutBaseChangeDiagram]
    exact pullback.condition

/-- Base change along `u` of a morphism `c` over `X`, with `g` the source of `c`, is an isomorphism
when the base change of `g` along `u` is a pullback square whose top map composes with `c` to the
base change of `w`. -/
private theorem isIso_pullback_map_of_isPullback {X B S : Scheme.{u}} (w : Over X) (g : B ⟶ X)
    (u : S ⟶ X) (c : B ⟶ w.left) (hc : c ≫ w.hom = g) {a : pullback w.hom u ⟶ B}
    (hPB : IsPullback a (pullback.snd w.hom u) g u) (ha : a ≫ c = pullback.fst w.hom u) :
    IsIso ((Over.pullback u).map (Over.homMk (U := Over.mk g) (V := w) c hc)).left := by
  let hPB' := IsPullback.of_hasPullback g u
  let e := hPB.isoIsPullback _ _ hPB'
  have hm : ((Over.pullback u).map (Over.homMk (U := Over.mk g) (V := w) c hc)).left =
      e.inv := by
    apply (IsPullback.of_hasPullback w.hom u).hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      change pullback.fst g u ≫ c = e.inv ≫ pullback.fst w.hom u
      rw [← ha, ← Category.assoc, hPB.isoIsPullback_inv_fst _ _ hPB']
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact (hPB.isoIsPullback_inv_snd _ _ hPB').symm
  rw [hm]
  exact ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩

/-- Base change of the comparison morphism along `X ⟶ Y ⨿_Z X` is an isomorphism: both sides
are pullbacks of `w` along that morphism. -/
theorem isIso_pullback_left_pushoutBaseChangeMap
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    IsIso (((Over.pullback (pushoutInl s)).map
      (Over.homMk (U := Over.mk (pushoutMap s (pushoutBaseChangeDiagram s w hw)))
        (V := w) (pushoutBaseChangeMap s w hw) (pushoutBaseChangeMap_comp_hom s w hw))).left) :=
  isIso_pullback_map_of_isPullback w _ _ _ _
    (pushoutMap_left_isPullback s (pushoutBaseChangeDiagram s w hw))
    (pushoutInl_comp_pushoutBaseChangeMap s w hw)

/-- Base change of the comparison morphism along `Y ⟶ Y ⨿_Z X` is an isomorphism: both sides
are pullbacks of `w` along that morphism. -/
theorem isIso_pullback_right_pushoutBaseChangeMap
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    IsIso (((Over.pullback (pushoutInr s)).map
      (Over.homMk (U := Over.mk (pushoutMap s (pushoutBaseChangeDiagram s w hw)))
        (V := w) (pushoutBaseChangeMap s w hw) (pushoutBaseChangeMap_comp_hom s w hw))).left) :=
  isIso_pullback_map_of_isPullback w _ _ _ _
    (pushoutMap_right_isPullback s (pushoutBaseChangeDiagram s w hw))
    (pushoutInr_comp_pushoutBaseChangeMap s w hw)

/-- The two canonical morphisms into the pushout `Y ⨿_Z X` are jointly surjective. -/
theorem pushoutInl_inr_jointly_surjective
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (p : pushoutScheme s) :
    p ∈ Set.range (pushoutInl s) ∨ p ∈ Set.range (pushoutInr s) := by
  by_cases hp : p ∈ Set.range (pushoutInr s)
  · exact Or.inr hp
  · let U : (pushoutScheme s).Opens :=
      ⟨(Set.range (pushoutInr s))ᶜ,
        (pushoutInr s).isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hpre : pushoutInr s ⁻¹ᵁ U = ⊥ := by
      apply TopologicalSpace.Opens.ext
      ext y
      show pushoutInr s y ∉ Set.range (pushoutInr s) ↔ False
      exact ⟨fun hy ↦ hy ⟨y, rfl⟩, False.elim⟩
    have hIso : IsIso (pushoutInl s ∣_ U) := pushoutInl_isIso_morphismRestrict s U hpre
    have hsurj : Function.Surjective (pushoutInl s ∣_ U) :=
      (TopCat.homeoOfIso (asIso ((pushoutInl s ∣_ U).base))).surjective
    obtain ⟨x, hx⟩ := hsurj ⟨p, hp⟩
    exact Or.inl ⟨x.1, by simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx⟩

/-- The comparison morphism is surjective. -/
theorem pushoutBaseChangeMap_surjective
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    Function.Surjective (pushoutBaseChangeMap s w hw) := by
  intro z
  have hcover : z ∈ Set.range (pullback.fst w.hom (pushoutInl s)) ∨
      z ∈ Set.range (pullback.fst w.hom (pushoutInr s)) := by
    simpa only [Scheme.Pullback.range_fst, Set.mem_preimage] using
      pushoutInl_inr_jointly_surjective s (w.hom z)
  rcases hcover with ⟨x, hx⟩ | ⟨y, hy⟩
  · refine ⟨pushoutInl (inducedSituation s (pushoutBaseChangeDiagram s w hw)) x, ?_⟩
    show (pushoutInl (inducedSituation s (pushoutBaseChangeDiagram s w hw)) ≫
      pushoutBaseChangeMap s w hw) x = z
    rw [pushoutInl_comp_pushoutBaseChangeMap]
    exact hx
  · refine ⟨pushoutInr (inducedSituation s (pushoutBaseChangeDiagram s w hw)) y, ?_⟩
    show (pushoutInr (inducedSituation s (pushoutBaseChangeDiagram s w hw)) ≫
      pushoutBaseChangeMap s w hw) y = z
    rw [pushoutInr_comp_pushoutBaseChangeMap]
    exact hy

/-- The comparison morphism is universally closed. -/
theorem pushoutBaseChangeMap_universallyClosed
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    UniversallyClosed (pushoutBaseChangeMap s w hw) := by
  have hUCInl : UniversallyClosed (pushoutInl s) :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp (pushoutInl_isIntegralHom s)).1
  have hleft : UniversallyClosed (pushoutInl
      (inducedSituation s (pushoutBaseChangeDiagram s w hw)) ≫ pushoutBaseChangeMap s w hw) := by
    rw [pushoutInl_comp_pushoutBaseChangeMap]
    exact universallyClosed_fst w.hom (pushoutInl s)
  have hright : UniversallyClosed (pushoutInr
      (inducedSituation s (pushoutBaseChangeDiagram s w hw)) ≫ pushoutBaseChangeMap s w hw) := by
    rw [pushoutInr_comp_pushoutBaseChangeMap]
    exact universallyClosed_fst w.hom (pushoutInr s)
  exact universallyClosed_of_jointly_surjective _ _ (pushoutBaseChangeMap s w hw)
    (pushoutInl_inr_jointly_surjective (inducedSituation s (pushoutBaseChangeDiagram s w hw)))

/-- The comparison morphism is finite: it is proper, by the previous two results, and locally
quasi-finite, because the composite with `w` is. -/
theorem pushoutBaseChangeMap_isFinite
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    IsFinite (pushoutBaseChangeMap s w hw) := by
  have hsep : IsSeparated w.hom := hw.2.1
  have hlft : LocallyOfFiniteType w.hom := hw.2.2.1
  have hqf : LocallyQuasiFinite w.hom := hw.2.2.2
  have hcompSep : IsSeparated (pushoutBaseChangeMap s w hw ≫ w.hom) := by
    rw [pushoutBaseChangeMap_comp_hom]
    infer_instance
  have h1 : IsSeparated (pushoutBaseChangeMap s w hw) :=
    (IsSeparated.comp_iff (f := pushoutBaseChangeMap s w hw) (g := w.hom)).mp hcompSep
  have hcompLft : LocallyOfFiniteType (pushoutBaseChangeMap s w hw ≫ w.hom) := by
    rw [pushoutBaseChangeMap_comp_hom]
    infer_instance
  have h2 : LocallyOfFiniteType (pushoutBaseChangeMap s w hw) :=
    locallyOfFiniteType_of_comp (pushoutBaseChangeMap s w hw) w.hom
  have hcompQf : LocallyQuasiFinite (pushoutBaseChangeMap s w hw ≫ w.hom) := by
    rw [pushoutBaseChangeMap_comp_hom]
    infer_instance
  have h3 : LocallyQuasiFinite (pushoutBaseChangeMap s w hw) :=
    (LocallyQuasiFinite.comp_iff (pushoutBaseChangeMap s w hw) w.hom).mp hcompQf
  have h4 : UniversallyClosed (pushoutBaseChangeMap s w hw) :=
    pushoutBaseChangeMap_universallyClosed s w hw
  have h5 : IsProper (pushoutBaseChangeMap s w hw) := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite (pushoutBaseChangeMap s w hw)

/-- A property stable under base change which holds for `w` holds for the three vertical
morphisms of the base change triple of `w`. -/
private theorem pushoutBaseChangeDiagram_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) (h : P w.hom) :
    P (pushoutBaseChangeDiagram s w hw).f ∧ P (pushoutBaseChangeDiagram s w hw).g ∧
      P (pushoutBaseChangeDiagram s w hw).h := by
  have hf : P (pushoutBaseChangeDiagram s w hw).f :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback w.hom (pushoutInl s)) h
  exact ⟨hf, MorphismProperty.of_isPullback (IsPullback.of_hasPullback w.hom (pushoutInr s)) h,
    MorphismProperty.of_isPullback (pushoutBaseChangeDiagram s w hw).left_isPullback hf⟩

/-- **Stacks Project, Tag 0ECL.** Every flat, separated, locally quasi-finite scheme over the
pushout is the pushout of its two base changes: the comparison morphism is an isomorphism. -/
theorem isIso_pushoutBaseChangeMap
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (w : Over (pushoutScheme s))
    (hw : Flat w.hom ∧ IsSeparated w.hom ∧
      LocallyOfFiniteType w.hom ∧ LocallyQuasiFinite w.hom) :
    IsIso (pushoutBaseChangeMap s w hw) := by
  let d := pushoutBaseChangeDiagram s w hw
  let c := pushoutBaseChangeMap s w hw
  let g := pushoutMap s d
  obtain ⟨hdf, hdg, hdh⟩ := pushoutBaseChangeDiagram_property @Flat s w hw hw.1
  have hg : Flat g := flat_pushoutMap s d
  have hwflat : Flat w.hom := hw.1
  have hfin : IsFinite c := pushoutBaseChangeMap_isFinite s w hw
  have hcomp : c ≫ w.hom = g := pushoutBaseChangeMap_comp_hom s w hw
  have hLocal : ∀ x : w.left, ∃ U : w.left.Opens, x ∈ U ∧ IsIso (c ∣_ U) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hmem, -⟩ :=
      (pushoutScheme s).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (w.hom x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      w.left.isBasis_affineOpens.exists_subset_of_mem_open
        (a := x) (show x ∈ w.hom ⁻¹ᵁ V from hmem) (w.hom ⁻¹ᵁ V).2
    have hApp : IsIso (c.app U) := by
      let UX := pushoutInl s ⁻¹ᵁ V
      let UY := pushoutInr s ⁻¹ᵁ V
      let UZ := s.j ⁻¹ᵁ UY
      have hS : IsAffineOpen (c ⁻¹ᵁ U) := hU.preimage c
      have hUX : IsAffineOpen UX := hV.preimage (pushoutInl s)
      have hUY : IsAffineOpen UY := hV.preimage (pushoutInr s)
      have hUZ : IsAffineOpen UZ := hUY.preimage s.j
      have eU : s.i ⁻¹ᵁ UX = s.j ⁻¹ᵁ UY :=
        congrArg (fun k : s.Z ⟶ pushoutScheme s ↦ k ⁻¹ᵁ V)
          (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
      have hsurj : Function.Surjective (s.i.appLE UX UZ eU.symm.le).hom := by
        have hcan : Function.Surjective (s.i.appLE UX (s.i ⁻¹ᵁ UX) le_rfl).hom := by
          simpa only [Scheme.Hom.appLE_eq_app] using s.i.app_surjective UX hUX
        exact (s.i.appLE_congr eU.symm.le rfl eU.symm
          (fun f ↦ Function.Surjective f.hom)).mpr hcan
      have hUΓ : IsPullback (pushoutInr s |>.appLE V UY le_rfl)
          (pushoutInl s |>.appLE V UX le_rfl)
          (s.j.appLE UY UZ le_rfl) (s.i.appLE UX UZ eU.symm.le) := by
        convert pushoutStructureSheaf_isPullback s V using 1
        · exact Scheme.Hom.appLE_eq_app (pushoutInr s)
        · exact Scheme.Hom.appLE_eq_app (pushoutInl s)
        · exact Scheme.Hom.appLE_eq_app s.j
        · show s.i.appLE UX UZ eU.symm.le =
            s.i.app UX ≫ eqToHom (congrArg (fun W ↦ Γ(s.Z, W)) eU)
          show s.i.app UX ≫ s.Z.presheaf.map (homOfLE eU.symm.le).op =
            s.i.app UX ≫ eqToHom (congrArg (fun W ↦ Γ(s.Z, W)) eU)
          rw [← eqToHom_map s.Z.presheaf (congrArg (fun W : s.Z.Opens ↦ Opposite.op W) eU)]
          congr 1
      have hSV' : c ⁻¹ᵁ U ≤ (c ≫ w.hom) ⁻¹ᵁ V :=
        (c.preimage_mono hUV).trans_eq (Scheme.Hom.comp_preimage c w.hom V).symm
      have hSV : c ⁻¹ᵁ U ≤ g ⁻¹ᵁ V := hcomp ▸ hSV'
      let Cobj : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(pushoutScheme s, V)) :=
        MorphismProperty.Under.mk ⊤ (w.hom.appLE V U hUV) (by
          rw [CommRingCat.flat_iff]
          exact w.hom.flat_appLE hV hU hUV)
      let Dobj : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(pushoutScheme s, V)) :=
        MorphismProperty.Under.mk ⊤ (g.appLE V (c ⁻¹ᵁ U) hSV) (by
          rw [CommRingCat.flat_iff]
          exact g.flat_appLE hV hS hSV)
      let fObj : Cobj ⟶ Dobj :=
        MorphismProperty.Under.homMk (c.appLE U (c ⁻¹ᵁ U) le_rfl) (by
          show w.hom.appLE V U hUV ≫ c.appLE U (c ⁻¹ᵁ U) le_rfl = g.appLE V (c ⁻¹ᵁ U) _
          rw [Scheme.Hom.appLE_comp_appLE c w.hom V U (c ⁻¹ᵁ U) hUV le_rfl]
          exact Scheme.Hom.appLE_congr_hom hcomp V (c ⁻¹ᵁ U) hSV' hSV)
      have hPushB : IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
          (pushoutInr s |>.appLE V UY le_rfl)).map fObj) :=
        isIso_sectionsPushoutMap_of_isIso_pullback g w.hom c (pushoutInr s) hcomp hV hU hUV
          (isIso_pullback_right_pushoutBaseChangeMap s w hw)
      have hPushA : IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
          (pushoutInl s |>.appLE V UX le_rfl)).map fObj) :=
        isIso_sectionsPushoutMap_of_isIso_pullback g w.hom c (pushoutInl s) hcomp hV hU hUV
          (isIso_pullback_left_pushoutBaseChangeMap s w hw)
      have hRing : IsIso fObj :=
        MilnorPatching.isIso_of_isIso_baseChange_of_isPullback
          (pushoutInr s |>.appLE V UY le_rfl).hom (pushoutInl s |>.appLE V UX le_rfl).hom
          (s.j.appLE UY UZ le_rfl).hom (s.i.appLE UX UZ eU.symm.le).hom
          hUΓ hsurj fObj hPushB hPushA
      have hForget := Functor.map_isIso (CategoryTheory.Under.forget
        (CommRingCat.of Γ(pushoutScheme s, V)))
        ((MorphismProperty.Under.forget CommRingCat.flat ⊤
          (CommRingCat.of Γ(pushoutScheme s, V))).map fObj)
      change IsIso (c.appLE U (c ⁻¹ᵁ U) le_rfl) at hForget
      simpa only [Scheme.Hom.app_eq_appLE] using hForget
    exact ⟨U, hxU, (isIso_morphismRestrict_iff_isIso_app c hU).2 hApp⟩
  exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict hLocal

/-- **Stacks Project, Tag 0ECL.** The pushout construction is an equivalence from the cartesian
triples with flat vertical morphisms to the flat, separated, locally quasi-finite schemes over
the pushout.  On objects it is the pushout of the triple together with its canonical morphism to
`Y ⨿_Z X`, and on morphisms it is the morphism of pushouts induced by the three components. -/
@[stacks 0ECL "flat equivalence"]
theorem flatTriple_pushout_equivalence
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    ∃ F : FlatCartesianTriple s ⥤ flatSchemesOver s,
      F.IsEquivalence ∧
      (∀ d, (F.obj d).1 = Over.mk (pushoutMap s d.1)) ∧
      (∀ (d e : FlatCartesianTriple s) (m : CartesianTripleHom d.1 e.1),
        ∃ k : pushoutScheme (inducedSituation s d.1) ⟶
            pushoutScheme (inducedSituation s e.1),
          HEq (((F.map m).1).left) k ∧
          (pushoutInl (inducedSituation s d.1) ≫ k =
            m.x ≫ pushoutInl (inducedSituation s e.1)) ∧
          (pushoutInr (inducedSituation s d.1) ≫ k =
            m.y ≫ pushoutInr (inducedSituation s e.1))) := by
  refine ⟨flatTripleToSchemesOver s, ?_, fun _ ↦ rfl, fun _ _ m ↦ ⟨triplePushoutMap m, HEq.rfl,
    pushoutInl_comp_triplePushoutMap m, pushoutInr_comp_triplePushoutMap m⟩⟩
  have hess : (flatTripleToSchemesOver s).EssSurj := by
    refine ⟨fun w ↦ ?_⟩
    have hw : Flat w.1.hom ∧ IsSeparated w.1.hom ∧
        LocallyOfFiniteType w.1.hom ∧ LocallyQuasiFinite w.1.hom := w.2
    obtain ⟨hdf, hdg, hdh⟩ := pushoutBaseChangeDiagram_property @Flat s w.1 hw hw.1
    obtain ⟨cinv, hc₁, hc₂⟩ := (isIso_pushoutBaseChangeMap s w.1 hw).out
    exact ⟨⟨pushoutBaseChangeDiagram s w.1 hw, ⟨hdf, hdg, hdh⟩⟩,
      ⟨ObjectProperty.isoMk _ (Over.isoMk ⟨pushoutBaseChangeMap s w.1 hw, cinv, hc₁, hc₂⟩
        (pushoutBaseChangeMap_comp_hom s w.1 hw))⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := hess }

/-- **Stacks Project, Tag 0ECL.** The pushout construction is an equivalence from the cartesian
triples with étale vertical morphisms to the étale, separated, locally quasi-finite schemes over
the pushout.  On objects it is the pushout of the triple together with its canonical morphism to
`Y ⨿_Z X`, and on morphisms it is the morphism of pushouts induced by the three components. -/
@[stacks 0ECL "étale equivalence"]
theorem etaleTriple_pushout_equivalence
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    ∃ F : EtaleCartesianTriple s ⥤ etaleSchemesOver s,
      F.IsEquivalence ∧
      (∀ d, (F.obj d).1 = Over.mk (pushoutMap s d.1)) ∧
      (∀ (d e : EtaleCartesianTriple s) (m : CartesianTripleHom d.1 e.1),
        ∃ k : pushoutScheme (inducedSituation s d.1) ⟶
            pushoutScheme (inducedSituation s e.1),
          HEq (((F.map m).1).left) k ∧
          (pushoutInl (inducedSituation s d.1) ≫ k =
            m.x ≫ pushoutInl (inducedSituation s e.1)) ∧
          (pushoutInr (inducedSituation s d.1) ≫ k =
            m.y ≫ pushoutInr (inducedSituation s e.1))) := by
  refine ⟨etaleTripleToSchemesOver s, ?_, fun _ ↦ rfl, fun _ _ m ↦ ⟨triplePushoutMap m, HEq.rfl,
    pushoutInl_comp_triplePushoutMap m, pushoutInr_comp_triplePushoutMap m⟩⟩
  have hess : (etaleTripleToSchemesOver s).EssSurj := by
    refine ⟨fun w ↦ ?_⟩
    obtain ⟨hEt, hsep, hlft, hqf⟩ : Etale w.1.hom ∧ IsSeparated w.1.hom ∧
        LocallyOfFiniteType w.1.hom ∧ LocallyQuasiFinite w.1.hom := w.2
    have hw : Flat w.1.hom ∧ IsSeparated w.1.hom ∧
        LocallyOfFiniteType w.1.hom ∧ LocallyQuasiFinite w.1.hom :=
      ⟨inferInstance, hsep, hlft, hqf⟩
    obtain ⟨hdf, hdg, hdh⟩ := pushoutBaseChangeDiagram_property @Etale s w.1 hw hEt
    obtain ⟨cinv, hc₁, hc₂⟩ := (isIso_pushoutBaseChangeMap s w.1 hw).out
    exact ⟨⟨pushoutBaseChangeDiagram s w.1 hw, ⟨hdf, hdg, hdh⟩⟩,
      ⟨ObjectProperty.isoMk _ (Over.isoMk ⟨pushoutBaseChangeMap s w.1 hw, cinv, hc₁, hc₂⟩
        (pushoutBaseChangeMap_comp_hom s w.1 hw))⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := hess }

end AlgebraicGeometry

end
