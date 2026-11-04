module

public import StacksFrontier.RingTheory.LocalCohomology.SupportInjectivity.Basic
import all StacksFrontier.RingTheory.LocalCohomology.SupportInjectivity.Basic
import all StacksFrontier.RingTheory.F6Sweep.LocalCohomologySupportSurjectivity

/-!
# Elements of local cohomology coming from larger supports

Let `I` be a finitely generated ideal of a commutative ring `A`, let `𝔭` be a prime ideal and let
`M` be an `A`-module. For `f` outside `𝔭` the supports `V(I + (f))` grow as `f` is replaced by a
multiple, so the local cohomology modules `Hⁱ_{V(I + (f))}(M)` form a filtered system over the
elements of `A \ 𝔭` ordered by divisibility, and the maps to `Hⁱ_{V(I)}(M)` induced by the
inclusions of supports assemble into a comparison map out of its colimit.

This file proves that the image of that comparison is exactly the kernel of localization at `𝔭`,
that the comparison is injective as soon as `Hⁱ⁻¹_{V(I)}(M)_𝔭` vanishes, and that it is an
isomorphism when `Hⁱ⁻¹_{V(I)}(M)_𝔭` and `Hⁱ_{V(I)}(M)_𝔭` both vanish.

Both inclusions of the first statement are elementary: a class supported on `V(I + (f))` is
annihilated by a power of `f`, hence dies after localization at `𝔭`; conversely a class killed by
some `f ∉ 𝔭` lifts along the fibre of the localization unit, which is the local cohomology of the
enlarged support. Injectivity is the enlargement step of the source: a class on `V(I + (f))` which
dies on `V(I)` already dies on `V(I + (f s))` for some `s ∉ 𝔭`, so it is zero in the colimit. The
isomorphism criterion combines the two.

## Main definitions

* `Stacks.LocalCohomology.MultiplicativeIndex` — the elements of a submonoid, ordered by
  divisibility.
* `Stacks.LocalCohomology.LocalCohomologyAwayColimitData` — the filtered diagram, its colimit and
  the comparison map, together with the equations identifying them.
* `Stacks.LocalCohomology.localCohomologyAwayColimitData` — the canonical such datum.

## Main results

* `Stacks.LocalCohomology.range_localCohomologyAwayComparison` — Tag 0DWU, part (1).
* `Stacks.LocalCohomology.localCohomologyAwayComparison_injective` — Tag 0DWU, part (2).
* `Stacks.LocalCohomology.localCohomologyAwayComparison_isIso` — Tag 0DWU, part (3).

## Implementation notes

The index type is a `Type` of the same universe as `A`, so the filtered colimit of the diagram
exists in `ModuleCat.{u} A` only when the module universe is at least that of `A`; the statements
are therefore single-universe, with `A : Type u` and `M : ModuleCat.{u} A`.

## References

* [Stacks Project, Tag 0DWU](https://stacks.math.columbia.edu/tag/0DWU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

open SupportSurjectivity SupportInjectivity

/-- The elements of a multiplicative subset of a commutative ring, ordered by divisibility. This
is the index of the filtered systems of Tags 0DWT and 0DWU. -/
def MultiplicativeIndex {A : Type u} [CommRing A] (S : Submonoid A) := S

/-- Divisibility in the ambient ring, as a preorder on the elements of a submonoid. -/
instance {A : Type u} [CommRing A] (S : Submonoid A) :
    Preorder (MultiplicativeIndex S) where
  le f g := (f : A) ∣ (g : A)
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans

/-- The unit of the submonoid is an index. -/
instance {A : Type u} [CommRing A] (S : Submonoid A) :
    Nonempty (MultiplicativeIndex S) := ⟨1⟩

/-- The product of two elements of the submonoid is a common upper bound for divisibility, so the
index is directed and hence filtered. -/
instance {A : Type u} [CommRing A] (S : Submonoid A) :
    IsDirected (MultiplicativeIndex S) (fun f g ↦ f ≤ g) :=
  ⟨fun f g ↦ ⟨⟨f * g, S.mul_mem f.property g.property⟩, ⟨g, rfl⟩, ⟨f, mul_comm _ _⟩⟩⟩

/-- The canonical divisibility-indexed system of local cohomology modules on the supports
`V(I + (f))` for `f ∉ 𝔭`, its colimit, and the comparison map to `Hⁱ_{V(I)}(M)`. The equations
ensure that both the transitions and the comparison are the maps induced by the inclusions of
supports. -/
structure LocalCohomologyAwayColimitData
    (A : Type u) [CommRing A] (I p : Ideal A) (hp : p.IsPrime) (hI : I.FG)
    (M : ModuleCat.{u} A) (i : ℤ) where
  /-- The filtered diagram of local cohomology modules on the enlarged supports. -/
  diagram : MultiplicativeIndex p.primeCompl ⥤ ModuleCat.{u} A
  /-- The value of the diagram at `f` is `Hⁱ_{V(I + (f))}(M)`. -/
  termIso (f : MultiplicativeIndex p.primeCompl) :
    diagram.obj f ≅ localCohomologyModule A (I ⊔ Ideal.span {f.val})
      (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) M i
  /-- The transition map for `f ∣ g` is the one induced by the inclusion
  `V(I + (g)) ⊆ V(I + (f))` of supports. -/
  transition (f g : MultiplicativeIndex p.primeCompl) (hfg : f ≤ g) :
    diagram.map (homOfLE hfg) =
      (termIso f).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
          (Stacks.Algebraization.localCohomologyComparison A (I ⊔ Ideal.span {f.val})
            (I ⊔ Ideal.span {g.val})
            (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val))
            (Submodule.FG.sup hI (Submodule.fg_span_singleton g.val))
            (by
              apply sup_le_sup_left
              rw [Ideal.span_le]
              rintro x (rfl : x = g.val)
              obtain ⟨a, ha⟩ := hfg
              rw [ha]
              exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f.val))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≫
        (termIso g).inv
  /-- A cocone on the diagram. -/
  cocone : Cocone diagram
  /-- The cocone is a colimit. -/
  isColimit : IsColimit cocone
  /-- The comparison map from the colimit to `Hⁱ_{V(I)}(M)`. -/
  comparison : cocone.pt ⟶ localCohomologyModule A I hI M i
  /-- The comparison restricted to the term at `f` is the map induced by the inclusion
  `V(I + (f)) ⊆ V(I)` of supports. -/
  comparison_fac (f : MultiplicativeIndex p.primeCompl) :
    cocone.ι.app f ≫ comparison =
      (termIso f).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
          (Stacks.Algebraization.localCohomologyComparison A (I ⊔ Ideal.span {f.val}) I
            (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) hI le_sup_left
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))

namespace AwayColimit

/-- Enlarging `I` by a multiple of `f` gives a smaller ideal than enlarging it by `f`. -/
private theorem enlarged_reverse_le {A : Type u} [CommRing A] {S : Submonoid A} (I : Ideal A)
    (f g : MultiplicativeIndex S) (hfg : f ≤ g) :
    I ⊔ Ideal.span {g.val} ≤ I ⊔ Ideal.span {f.val} :=
  sup_le_sup_left (Ideal.span_singleton_le_span_singleton.mpr hfg) I

/-- The comparison of a support with itself is the identity on local cohomology objects. -/
private theorem mapOfLE_self {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) :
    mapOfLE A I I hI hI le_rfl M = 𝟙 _ := by
  let P := Dualizing.derivedPowerTorsionProperty A I hI
  let adj := Dualizing.localCohomologyAdjunction A I hI
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  let G := (Dualizing.localCohomologyRightAdjoint A I hI).1
  have hW : restrictLocalCohomologySupport A I I hI hI le_rfl M = G.obj X := by
    apply CategoryTheory.ObjectProperty.FullSubcategory.ext
    rfl
  have hc : (adj.homEquiv (G.obj X) X) (adj.counit.app X) = 𝟙 _ := by
    apply (adj.homEquiv (G.obj X) X).symm.injective
    simpa using (adj.homEquiv_counit (g := 𝟙 (G.obj X))).symm
  have h : adj.homEquiv (restrictLocalCohomologySupport A I I hI hI le_rfl M) X
      (adj.counit.app X) = 𝟙 (G.obj X) := by
    cases hW
    exact hc
  change P.ι.map
    (adj.homEquiv (restrictLocalCohomologySupport A I I hI hI le_rfl M) X
      (adj.counit.app X)) = P.ι.map (𝟙 (G.obj X))
  rw [h]
  exact P.ι.map_id _

/-- The map on local cohomology modules induced by the identity inclusion is the identity. -/
private theorem localCohomologyModuleMapOfLE_self {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (M : ModuleCat.{u} A) (i : ℤ) :
    localCohomologyModuleMapOfLE A I I hI hI le_rfl M i = 𝟙 _ := by
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    (mapOfLE A I I hI hI le_rfl M) = _
  rw [mapOfLE_self]
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map_id _

end AwayColimit

open AwayColimit in
/-- The canonical filtered system of local cohomology modules on the supports `V(I + (f))` for
`f ∉ 𝔭`, its colimit and the comparison map of Tag 0DWU. -/
@[no_expose]
def localCohomologyAwayColimitData
    (A : Type u) [CommRing A] (I p : Ideal A) (hp : p.IsPrime) (hI : I.FG)
    (M : ModuleCat.{u} A) (i : ℤ) :
    LocalCohomologyAwayColimitData A I p hp hI M i := by
  classical
  let Index := MultiplicativeIndex p.primeCompl
  let D : Index ⥤ ModuleCat.{u} A := {
    obj := fun f => localCohomologyModule A (I ⊔ Ideal.span {f.val})
      (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) M i
    map := fun {f g} hfg => localCohomologyModuleMapOfLE A (I ⊔ Ideal.span {g.val})
      (I ⊔ Ideal.span {f.val})
      (Submodule.FG.sup hI (Submodule.fg_span_singleton g.val))
      (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val))
      (enlarged_reverse_le I f g hfg.le) M i
    map_id := fun f => localCohomologyModuleMapOfLE_self (I ⊔ Ideal.span {f.val})
      (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) M i
    map_comp := fun {f g k} hfg hgk =>
      (localCohomologyModuleMapOfLE_comp (I ⊔ Ideal.span {k.val})
        (I ⊔ Ideal.span {g.val}) (I ⊔ Ideal.span {f.val})
        (Submodule.FG.sup hI (Submodule.fg_span_singleton k.val))
        (Submodule.FG.sup hI (Submodule.fg_span_singleton g.val))
        (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val))
        (enlarged_reverse_le I g k hgk.le)
        (enlarged_reverse_le I f g hfg.le) M i).symm }
  let C : Cocone D := {
    pt := localCohomologyModule A I hI M i
    ι := {
      app f := localCohomologyModuleMapOfLE A I (I ⊔ Ideal.span {f.val}) hI
        (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) le_sup_left M i
      naturality := fun f g hfg =>
        localCohomologyModuleMapOfLE_comp I (I ⊔ Ideal.span {g.val})
          (I ⊔ Ideal.span {f.val}) hI
          (Submodule.FG.sup hI (Submodule.fg_span_singleton g.val))
          (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) le_sup_left
          (enlarged_reverse_le I f g hfg.le) M i } }
  let hc := colimit.isColimit D
  refine ⟨D, fun f => Iso.refl _, ?_, colimit.cocone D, hc, hc.desc C, ?_⟩
  · intro f g hfg
    simp only [Iso.refl_hom, Iso.refl_inv]
    rfl
  · intro f
    change colimit.ι D f ≫ hc.desc C = 𝟙 (D.obj f) ≫ C.ι.app f
    rw [← colimit.cocone_ι, Category.id_comp, hc.fac C f]

namespace AwayColimit

/-- The comparison map, evaluated on the image of an element of the term at `f`, is the map
induced by the inclusion `V(I + (f)) ⊆ V(I)` of supports. -/
private theorem comparison_fac_apply
    (A : Type u) [CommRing A] (I p : Ideal A) (hp : p.IsPrime) (hI : I.FG)
    (M : ModuleCat.{u} A) (i : ℤ)
    (D : LocalCohomologyAwayColimitData A I p hp hI M i)
    (f : MultiplicativeIndex p.primeCompl) (x : D.diagram.obj f) :
    D.comparison.hom ((D.cocone.ι.app f).hom x) =
      (localCohomologyModuleMapOfLE A I (I ⊔ Ideal.span {f.val}) hI
        (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) le_sup_left M i).hom
        ((D.termIso f).hom x) := by
  calc
    D.comparison.hom ((D.cocone.ι.app f).hom x) =
        (D.cocone.ι.app f ≫ D.comparison).hom x := by simp
    _ = ((D.termIso f).hom ≫
        localCohomologyModuleMapOfLE A I (I ⊔ Ideal.span {f.val}) hI
          (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val))
            le_sup_left M i).hom x := by
      rw [D.comparison_fac f]
    _ = _ := by simp

/-- Everything in the image of the comparison dies after localization at `𝔭`: a class on
`V(I + (f))` is annihilated by a power of `f`, which is outside `𝔭`. -/
private theorem comparison_kills_localization
    (A : Type u) [CommRing A] (I p : Ideal A) (hp : p.IsPrime) (hI : I.FG)
    (M : ModuleCat.{u} A) (i : ℤ)
    (D : LocalCohomologyAwayColimitData A I p hp hI M i) (z : D.cocone.pt) :
    (LocalizedModule.mkLinearMap p.primeCompl (localCohomologyModule A I hI M i))
      (D.comparison.hom z) = 0 := by
  obtain ⟨f, x, hx⟩ := isColimit_exists_rep_moduleCat D.diagram D.cocone D.isColimit z
  let J := I ⊔ Ideal.span {f.val}
  let hJ : J.FG := Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)
  let ψ := localCohomologyModuleMapOfLE A I J hI hJ le_sup_left M i
  have hfac : D.comparison.hom ((D.cocone.ι.app f).hom x) =
      ψ.hom ((D.termIso f).hom x) := by
    simpa [J, hJ, ψ] using comparison_fac_apply A I p hp hI M i D f x
  rw [← hx, hfac]
  obtain ⟨n, hn, hkill⟩ :=
    ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).property i
      ((D.termIso f).hom x)
  have hkill' : f.val ^ n • ψ.hom ((D.termIso f).hom x) = 0 := by
    rw [← ψ.hom.map_smul, hkill _ (Ideal.pow_mem_pow (Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self f.val)) n)]
    simp
  rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff]
  exact ⟨f.val ^ n, p.primeCompl.pow_mem f.property n, hkill'⟩

end AwayColimit

open AwayColimit in
/-- **Stacks 0DWU, part (1).** The image of the comparison out of the colimit of the local
cohomology modules on the supports `V(I + (f))`, for `f` outside the prime `𝔭`, is the kernel of
localization at `𝔭`. -/
@[stacks 0DWU "part (1)"]
theorem range_localCohomologyAwayComparison
    (A : Type u) [CommRing A] (I p : Ideal A) (hp : p.IsPrime) (hI : I.FG)
    (M : ModuleCat.{u} A) (i : ℤ) (_hi : 0 ≤ i) :
    LinearMap.range (localCohomologyAwayColimitData A I p hp hI M i).comparison.hom =
      LinearMap.ker (LocalizedModule.mkLinearMap p.primeCompl
        (localCohomologyModule A I hI M i)) := by
  let D := localCohomologyAwayColimitData A I p hp hI M i
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_ker.mpr (comparison_kills_localization A I p hp hI M i D z)
  · obtain ⟨s, hs, hkill⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp hx
    obtain ⟨z, hz⟩ := exists_lift_of_smul_eq_zero A I hI M i s x hkill
    let f : MultiplicativeIndex p.primeCompl := ⟨s, hs⟩
    refine LinearMap.mem_range.mpr ⟨(D.cocone.ι.app f).hom ((D.termIso f).inv.hom z), ?_⟩
    rw [comparison_fac_apply]
    have hcancel : (D.termIso f).hom ((D.termIso f).inv.hom z) = z :=
      congrArg (fun g => g.hom z) (D.termIso f).inv_hom_id
    rw [hcancel]
    simpa [f] using hz

open AwayColimit in
/-- **Stacks 0DWU, part (2).** If `Hⁱ⁻¹_{V(I)}(M)` vanishes after localization at the prime `𝔭`,
the comparison out of the colimit is injective. -/
@[stacks 0DWU "part (2)"]
theorem localCohomologyAwayComparison_injective
    (A : Type u) [CommRing A] (I p : Ideal A) (hp : p.IsPrime) (hI : I.FG)
    (M : ModuleCat.{u} A) (i : ℤ) (_hi : 0 ≤ i)
    (hvan : Subsingleton
      (LocalizedModule p.primeCompl (localCohomologyModule A I hI M (i - 1)))) :
    Function.Injective
      (localCohomologyAwayColimitData A I p hp hI M i).comparison.hom := by
  let D := localCohomologyAwayColimitData A I p hp hI M i
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨f, w, hw⟩ := isColimit_exists_rep_moduleCat D.diagram D.cocone D.isColimit z
  have hx : (localCohomologyModuleMapOfLE A I (I ⊔ Ideal.span {f.val}) hI
      (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) le_sup_left M i).hom
      ((D.termIso f).hom.hom w) = 0 := by
    rw [← comparison_fac_apply, hw, hz]
  obtain ⟨s, hs⟩ := localCohomology_kernel_eventually_zero A I p.primeCompl hI M i hvan
    f.val ((D.termIso f).hom.hom w) hx
  let g : MultiplicativeIndex p.primeCompl :=
    ⟨f.val * s.val, p.primeCompl.mul_mem f.property s.property⟩
  have hfg : f ≤ g := ⟨s.val, rfl⟩
  have ht : (D.diagram.map (homOfLE hfg)).hom w = 0 := by
    rw [D.transition f g hfg, ModuleCat.comp_apply, ModuleCat.comp_apply]
    change (D.termIso g).inv.hom
      ((localCohomologyModuleMapOfLE A (I ⊔ Ideal.span {(g : A)})
        (I ⊔ Ideal.span {f.val})
        (Submodule.FG.sup hI (Submodule.fg_span_singleton (g : A)))
        (Submodule.FG.sup hI (Submodule.fg_span_singleton f.val)) _ M i).hom
          ((D.termIso f).hom.hom w)) = 0
    rw [hs, map_zero]
  rw [← hw]
  calc
    (D.cocone.ι.app f).hom w =
        (D.cocone.ι.app g).hom ((D.diagram.map (homOfLE hfg)).hom w) :=
      (congrArg (fun k => k.hom w) (D.cocone.w (homOfLE hfg))).symm
    _ = 0 := by rw [ht, map_zero]

/-- **Stacks 0DWU, part (3).** If `Hⁱ⁻¹_{V(I)}(M)` and `Hⁱ_{V(I)}(M)` both vanish after
localization at the prime `𝔭`, the comparison out of the colimit is an isomorphism. -/
@[stacks 0DWU "part (3)"]
theorem localCohomologyAwayComparison_isIso
    (A : Type u) [CommRing A] (I p : Ideal A) (hp : p.IsPrime) (hI : I.FG)
    (M : ModuleCat.{u} A) (i : ℤ) (hi : 0 ≤ i)
    (hvanPrev : Subsingleton
      (LocalizedModule p.primeCompl (localCohomologyModule A I hI M (i - 1))))
    (hvan : Subsingleton
      (LocalizedModule p.primeCompl (localCohomologyModule A I hI M i))) :
    IsIso (localCohomologyAwayColimitData A I p hp hI M i).comparison := by
  let D := localCohomologyAwayColimitData A I p hp hI M i
  have hsurj : Function.Surjective D.comparison.hom := by
    rw [← LinearMap.range_eq_top, range_localCohomologyAwayComparison A I p hp hI M i hi,
      LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)]
  have _ : Mono D.comparison := (ModuleCat.mono_iff_injective _).2
    (localCohomologyAwayComparison_injective A I p hp hI M i hi hvanPrev)
  have _ : Epi D.comparison := (ModuleCat.epi_iff_surjective _).2 hsurj
  exact isIso_of_mono_of_epi _

end Stacks.LocalCohomology
