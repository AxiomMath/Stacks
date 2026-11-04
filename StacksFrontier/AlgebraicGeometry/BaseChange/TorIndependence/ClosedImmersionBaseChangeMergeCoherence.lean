module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeLocalIdentity
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeLocalReduction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkSource

/-!
# Tor-independent base change along a closed immersion: the transport of the image point

This file proves `Stacks.Cohomology.ClosedImmersionBaseChange.TransportCoherenceAt`, the coherence
between the transport of the derived stalk of `Ri_*` along the equality `i' ≫ f = g ≫ i` spelled
as `eqToHom` and the same transport spelled geometrically, deduces from it the merge coherence
`Stacks.Cohomology.ClosedImmersionBaseChange.MergeCoherenceAt` and the local base change identity,
and concludes Stacks 0E23: Tor-independent base change along a closed immersion.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.TransportCoherenceAt`: the transport of the image
  point.  On the left, the merge of the extensions of scalars for `i'` and `f` followed by the
  transport along the diagonal of the square and the transport along
  `Stacks.ModuleSkyscraper.stalkMap_hom_comp`.  On the right, the *untransported* merge of the two
  germ maps, then the transport of the derived stalk functor from `f (i' w)` to `i (g w)`, then
  the absorption of the germ comparison into the composite germ map, then the transport along
  `Stacks.Cohomology.ClosedImmersionBaseChange.stalkMap_ringHom_square`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.mergeCoherenceAt_of_transport`: it implies
  `MergeCoherenceAt`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.transportCoherenceAt`: **the transport of the image
  point holds.**
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEqQKFlat_holds`: the equality
  of derived stalks below `DerivedCategory.Q` holds.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeSquare_of_torIndependent`
  and `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso`: Tor-independent
  base change along a closed immersion.

## Implementation notes

`StacksDraft.DerivedStalkMergeCoherenceChase.transportReduce` and `transportCollapse` are stated at
free objects of abstract categories.  The concrete terms are components of thirty-argument
composites in four derived categories, and a chase that asks the elaborator to assign them while
unifying two spellings of degreewise extension of scalars exhausts the heartbeat budget.  Moreover
the germ map of `i' ≫ f` at `w` and the germ map of `f` at `i' w` are interchangeable only at
default transparency, so a `rw` whose motive abstracts over the derived stalk of `Ri_*` is not
type-correct and every rewrite on the concrete equation fails.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedRingIso
open StacksDraft.DerivedExtensionScalarsComp
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

namespace StacksDraft.DerivedStalkMergeCoherenceChase

variable {A Ma Mb Mp : Type*} [Category A] [Category Ma] [Category Mb] [Category Mp]

/-- **The merge coherence reduced to the transport of the image point.**  Read `Tch` as derived
extension of scalars along the germ map of `i'`, `Tps` as the same along the germ map of `f`,
`Rst` as derived restriction of scalars along the germ comparison of the two presentations of the
image point, `Tcp`, `Tce` and `Tgh` as derived extension of scalars along the composite of the two
germ maps, along that composite precomposed with the germ comparison, and along the composite of
the germ maps of `g` and `i`, and `Lgg` as the functor Stacks 0661 is stated at. -/
theorem transportReduce (Tch : Mp ⥤ A) (Tps : Mb ⥤ Mp) (Rst : Ma ⥤ Mb)
    (Tcp : Mb ⥤ A) (Tce : Ma ⥤ A) (Tgh : Ma ⥤ A) (Lgg : Ma ⥤ Mp)
    {t₀ : Mb} {s₀ s₁ s₂ : Ma} {y₀ : Mp} {x₁ x₂ : A}
    (pq : s₀ ⟶ s₁) (G₂ : s₁ ⟶ s₂) (B : t₀ ⟶ Rst.obj s₀) (τ : t₀ ⟶ Rst.obj s₂)
    (A₁ : Tch.obj (Tps.obj t₀) ⟶ x₁) (tr₂ : x₁ ⟶ x₂) (tr₃ : x₂ ⟶ Tgh.obj s₀)
    (pi : Tps.obj t₀ ⟶ y₀) (A' : y₀ ⟶ Tps.obj t₀) (SRC : y₀ ⟶ Lgg.obj s₁)
    (RI₀ : Tps.obj (Rst.obj s₁) ⟶ Lgg.obj s₁) (RI : Tps.obj (Rst.obj s₂) ⟶ Lgg.obj s₂)
    (CI : Tch.obj (Tps.obj t₀) ⟶ Tcp.obj t₀)
    (CI' : Tch.obj (Tps.obj (Rst.obj s₂)) ⟶ Tcp.obj (Rst.obj s₂))
    (CIr : Tch.obj (Lgg.obj s₂) ⟶ Tce.obj s₂) (R₃ : Tce.obj s₂ ⟶ Tgh.obj s₂)
    (RJ₀ : Tcp.obj (Rst.obj s₀) ⟶ Tce.obj s₀) (RJ₂ : Tcp.obj (Rst.obj s₂) ⟶ Tce.obj s₂)
    (e₀ : Tce.obj s₀ ⟶ Tgh.obj s₀)
    (hsrc : SRC = A' ≫ Tps.map B ≫ Tps.map (Rst.map pq) ≫ RI₀)
    (hpi : pi ≫ A' = CategoryStruct.id (Tps.obj t₀))
    (hRI : Tps.map (Rst.map G₂) ≫ RI = RI₀ ≫ Lgg.map G₂)
    (hcoh : Tch.map RI ≫ CIr = CI' ≫ RJ₂)
    (hτ : τ = B ≫ Rst.map (pq ≫ G₂))
    (hCI : Tch.map (Tps.map τ) ≫ CI' = CI ≫ Tcp.map τ)
    (hRJ : Tcp.map (Rst.map (pq ≫ G₂)) ≫ RJ₂ = RJ₀ ≫ Tce.map (pq ≫ G₂))
    (hR₃ : Tce.map (pq ≫ G₂) ≫ R₃ = e₀ ≫ Tgh.map (pq ≫ G₂))
    (hres : A₁ ≫ tr₂ ≫ tr₃ = CI ≫ Tcp.map B ≫ RJ₀ ≫ e₀) :
    A₁ ≫ tr₂ ≫ tr₃ ≫ Tgh.map (pq ≫ G₂) =
      Tch.map (pi ≫ SRC ≫ Lgg.map G₂) ≫ CIr ≫ R₃ := by
  have hone : pi ≫ SRC ≫ Lgg.map G₂ = Tps.map τ ≫ RI := by
    calc pi ≫ SRC ≫ Lgg.map G₂
        = (pi ≫ A') ≫ Tps.map B ≫ Tps.map (Rst.map pq) ≫ RI₀ ≫ Lgg.map G₂ := by
          rw [hsrc]; simp
      _ = Tps.map B ≫ Tps.map (Rst.map pq) ≫ RI₀ ≫ Lgg.map G₂ := by rw [hpi]; simp
      _ = Tps.map B ≫ Tps.map (Rst.map pq) ≫ Tps.map (Rst.map G₂) ≫ RI := by rw [hRI]
      _ = Tps.map τ ≫ RI := by rw [hτ]; simp
  calc A₁ ≫ tr₂ ≫ tr₃ ≫ Tgh.map (pq ≫ G₂)
      = (A₁ ≫ tr₂ ≫ tr₃) ≫ Tgh.map (pq ≫ G₂) := by simp
    _ = CI ≫ Tcp.map B ≫ RJ₀ ≫ e₀ ≫ Tgh.map (pq ≫ G₂) := by rw [hres]; simp
    _ = CI ≫ Tcp.map B ≫ RJ₀ ≫ Tce.map (pq ≫ G₂) ≫ R₃ := by rw [hR₃]
    _ = CI ≫ Tcp.map B ≫ Tcp.map (Rst.map (pq ≫ G₂)) ≫ RJ₂ ≫ R₃ := by
        rw [← reassoc_of% hRJ]
    _ = CI ≫ Tcp.map τ ≫ RJ₂ ≫ R₃ := by rw [hτ]; simp
    _ = (Tch.map (Tps.map τ) ≫ CI') ≫ RJ₂ ≫ R₃ := by rw [hCI]; simp
    _ = Tch.map (Tps.map τ) ≫ Tch.map RI ≫ CIr ≫ R₃ := by
        simp only [Category.assoc]; rw [← reassoc_of% hcoh]
    _ = Tch.map (pi ≫ SRC ≫ Lgg.map G₂) ≫ CIr ≫ R₃ := by rw [hone]; simp

/-- **The transport of the image point, once the merge and the residue are known.** Read `mh` as
the transported merge of the two extensions of scalars, `c` as the untransported one, `m` and `r`
as the transport of the derived stalk functor and the absorption of the germ comparison, and the
five equalities of objects as the transports the two sides are composites of. If the untransported
merge is the transported one followed by `eqToHom pu`, and the residue is `eqToHom pv`, then the
two sides agree. -/
theorem transportCollapse {𝒞 : Type*} [Category 𝒞] {Xo Y₁ Y₂ Y₃ Z₁ Z₂ Z₃ : 𝒞}
    (mh : Xo ⟶ Y₁) (c : Xo ⟶ Z₁) (m : Z₁ ⟶ Z₂) (r : Z₂ ⟶ Z₃)
    (p₂ : Y₁ = Y₂) (p₃ : Y₂ = Y₃) (pu : Y₁ = Z₁) (pv : Z₁ = Z₃) (p₄ : Z₃ = Y₃)
    (hc : c = mh ≫ eqToHom pu) (hr : m ≫ r = eqToHom pv) :
    mh ≫ eqToHom p₂ ≫ eqToHom p₃ = c ≫ m ≫ r ≫ eqToHom p₄ := by
  rw [hc, reassoc_of% hr]
  simp only [Category.assoc, eqToHom_trans]

end StacksDraft.DerivedStalkMergeCoherenceChase

universe u

namespace Stacks.Cohomology.ClosedImmersionBaseChange

attribute [local instance] HasDerivedCategory.standard

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

open Stacks.Cohomology.DerivedBaseChange in
/-- **The transport of the image point.**

On the left, the merge of the extensions of scalars for `i'` and `f`, the transport along the
diagonal of the square and the transport along
`Stacks.ModuleSkyscraper.stalkMap_hom_comp` for `g` and `i` — that is, the transport of the
derived stalk of `Ri_*` along the equality of morphisms `i' ≫ f = g ≫ i`.

On the right, the *untransported* merge of the two germ maps, then the transport of the derived
stalk functor from `f (i' w)` to `i (g w)` (`derivedStalkFunctorCongr`), then the absorption of
the germ comparison into the composite germ map
(`StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso`), then the transport along
`stalkMap_ringHom_square`.

Both sides are the same transport, spelled as `eqToHom` on the left and geometrically on the
right. -/
abbrev TransportCoherenceAt (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) : Prop :=
  letI := isClosedImmersion_of_isPullback sq
  (AlgebraicGeometry.derivedStalkExtensionCompIso i' f w).hom.app
        ((AlgebraicGeometry.derivedStalkFunctor (f (i' w))).obj
          ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
      eqToHom (congrArg (fun ψ : Z' ⟶ X =>
          (totalDerivedExtensionScalars.{u, u, u} (ψ.stalkMap w).hom).functor.obj
            ((AlgebraicGeometry.derivedStalkFunctor (ψ w)).obj
              ((derivedPushforward i.toLRSHom.toShHom).obj
                (DerivedCategory.Q.obj P)))) sq.w) ≫
        eqToHom (congrArg (fun φ =>
            (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
              ((AlgebraicGeometry.derivedStalkFunctor (i (g w))).obj
                ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))))
          (Stacks.ModuleSkyscraper.stalkMap_hom_comp g i w)) =
    (derivedExtensionScalarsCompIso (f.stalkMap (i' w)).hom (i'.stalkMap w).hom).hom.app
        ((AlgebraicGeometry.derivedStalkFunctor (f (i' w))).obj
          ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
      (totalDerivedExtensionScalars.{u, u, u}
            ((i'.stalkMap w).hom.comp (f.stalkMap (i' w)).hom)).functor.map
          ((derivedStalkFunctorCongr (ptEq sq w).symm).inv.app
            ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
        (derivedExtensionScalarsRestrictIso
              (X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w))).hom.hom
              (X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w).symm)).hom.hom
              (stalkCongr_symm_hom_hom_apply (ptEq sq w))
              (stalkCongr_hom_symm_hom_apply (ptEq sq w))
              ((i'.stalkMap w).hom.comp (f.stalkMap (i' w)).hom)).hom.app
            ((AlgebraicGeometry.derivedStalkFunctor (i (g w))).obj
              ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
          eqToHom (congrArg (fun φ =>
              (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
                ((AlgebraicGeometry.derivedStalkFunctor (i (g w))).obj
                  ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))))
            (stalkMap_ringHom_square sq w (ptEq sq w)).symm)

open Stacks.Cohomology.DerivedBaseChange StacksDraft.DerivedStalkMergeCoherenceChase in
/-- **The transport of the image point.**  `TransportCoherenceAt` holds: the transport spelled as
`eqToHom` and the same transport spelled geometrically agree. -/
theorem transportCoherenceAt (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) : TransportCoherenceAt sq w P := by
  have := isClosedImmersion_of_isPullback sq
  exact transportCollapse _ _ _ _ _ _ _ _ _
    (AlgebraicGeometry.derivedExtensionScalarsCompIso_hom_app_eq i' f w _)
    (transportResidue (ptEq sq w) (ptEq sq w).symm _
      (stalkCongr_symm_hom_hom_apply (ptEq sq w))
      (stalkCongr_hom_symm_hom_apply (ptEq sq w)) _)

open Stacks.Cohomology.DerivedBaseChange StacksDraft.DerivedStalkMergeCoherenceChase in
/-- **The transport of the image point implies the merge coherence `MergeCoherenceAt`.** -/
theorem mergeCoherenceAt_of_transport (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) (ht : TransportCoherenceAt sq w P) :
    MergeCoherenceAt sq w P := by
  have := isClosedImmersion_of_isPullback sq
  exact transportReduce
    (Tch := (totalDerivedExtensionScalars.{u, u, u} (i'.stalkMap w).hom).functor)
    (Tps := (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor)
    (Rst := (ModuleCat.restrictScalars.{u, u, u}
      (X.presheaf.stalkCongr
        (Inseparable.of_eq (ptEq sq w).symm)).hom.hom).mapDerivedCategory)
    (Tcp := (totalDerivedExtensionScalars.{u, u, u}
      ((i'.stalkMap w).hom.comp (f.stalkMap (i' w)).hom)).functor)
    (Tce := (totalDerivedExtensionScalars.{u, u, u}
      ((i'.stalkMap w).hom.comp (ringRR' w (ptEq sq w)))).functor)
    (Tgh := (totalDerivedExtensionScalars.{u, u, u}
      ((g.stalkMap w).hom.comp (i.stalkMap (g w)).hom)).functor)
    (Lgg := Lg w (ptEq sq w))
    (hsrc := derivedStalkSourceIso_hom_app w (ptEq sq w) (DerivedCategory.Q.obj P))
    (hpi := Iso.inv_hom_id_app (AlgebraicGeometry.derivedPullbackStalkIso f (i' w)) _)
    (hRI := (derivedExtensionStalkIso w (ptEq sq w)).hom.naturality _)
    (hcoh := derivedExtensionStalkIso_hom_app_comp_compIso w (ptEq sq w) _)
    (hτ := rfl)
    (hCI := (derivedExtensionScalarsCompIso (f.stalkMap (i' w)).hom
      (i'.stalkMap w).hom).hom.naturality _)
    (hRJ := (derivedExtensionScalarsRestrictIso
      (X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w))).hom.hom
      (X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w).symm)).hom.hom
      (stalkCongr_symm_hom_hom_apply (ptEq sq w))
      (stalkCongr_hom_symm_hom_apply (ptEq sq w))
      ((i'.stalkMap w).hom.comp (f.stalkMap (i' w)).hom)).hom.naturality _)
    (hR₃ := functor_map_comp_eqToHom _ _ (stalkMap_ringHom_square sq w (ptEq sq w)).symm _)
    (hres := ht)

open Stacks.Cohomology.DerivedBaseChange in
/-- **The transport of the image point implies the local base change identity
`LocalBaseChangeIdentityAt`.** -/
theorem localBaseChangeIdentityAt_of_transport (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) (ht : TransportCoherenceAt sq w P) :
    LocalBaseChangeIdentityAt sq w P :=
  localBaseChangeIdentityAt_of_merge sq w P
    (mergeIdentityAt_of_coherence sq w P (mergeCoherenceAt_of_transport sq w P ht))

/-! ### Stacks 0E23 -/

open Stacks.Cohomology.DerivedBaseChange in
/-- **The local base change identity `LocalBaseChangeIdentityAt` holds.** -/
theorem localBaseChangeIdentityAt_holds (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) :
    LocalBaseChangeIdentityAt sq w P :=
  localBaseChangeIdentityAt_of_transport sq w P (transportCoherenceAt sq w P)

open Stacks.Cohomology.DerivedBaseChange in
/-- **The equality `DerivedStalkBaseChangeEqQKFlat` of derived stalks below
`DerivedCategory.Q` holds.** -/
theorem derivedStalkBaseChangeEqQKFlat_holds (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] :
    DerivedStalkBaseChangeEqQKFlat sq :=
  fun w P _ => derivedStalkBaseChangeEqQAt_of_local sq w P (localBaseChangeIdentityAt_holds sq w P)

open Stacks.Cohomology.DerivedBaseChange in
/-- In a cartesian square of schemes with `i` a closed immersion and `Z`, `X'` Tor independent
over `X`, the canonical morphism of functors `Ri_* ⋙ Lf^* ⟶ Lg^* ⋙ Ri'_*` of Stacks 08HY is an
isomorphism. -/
@[stacks 0E23 "the canonical base change map Lf^* ∘ Ri_* ⟶ Ri'_* ∘ Lg^* is invertible"]
theorem isIso_derivedBaseChangeSquare_of_torIndependent (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f) :
    IsIso (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)) :=
  isIso_derivedBaseChangeSquare_of_Q_kFlat sq htor (derivedStalkBaseChangeEqQKFlat_holds sq)

open Stacks.Cohomology.DerivedBaseChange in
/-- In a cartesian square of schemes with `i` a closed immersion and `Z`, `X'` Tor independent
over `X`, the canonical derived base change map `Lf^*(Ri_*K) ⟶ Ri'_*(Lg^*K)` of Stacks 08HY is
invertible at every `K`. -/
theorem isIso_derivedBaseChangeMap_of_torIndependent (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (K : DerivedCategory Z.Modules) :
    IsIso (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) K) :=
  isIso_derivedBaseChangeMap_of_onImage sq K fun w =>
    isIso_derivedStalk_derivedBaseChangeMap_of_eq sq htor
      (derivedStalkBaseChangeEq_of_Q_kFlat sq (derivedStalkBaseChangeEqQKFlat_holds sq)) w K

open Stacks.Cohomology.DerivedBaseChange in
/-- **Tor-independent base change along a closed immersion.**  For a cartesian square with `i` a
closed immersion and `Z`, `X'` Tor independent over `X`, the functors `Lf^* ∘ Ri_*` and
`Ri'_* ∘ Lg^*` from `D(𝒪_Z)` to `D(𝒪_{X'})` are isomorphic, by the canonical derived base change
map of Stacks 08HY. -/
@[stacks 0E23]
def derivedBaseChangeSquareIso (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i'.toLRSHom.toShHom :=
  derivedBaseChangeSquareIsoOfEq sq htor
    (derivedStalkBaseChangeEq_of_Q_kFlat sq (derivedStalkBaseChangeEqQKFlat_holds sq))

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
