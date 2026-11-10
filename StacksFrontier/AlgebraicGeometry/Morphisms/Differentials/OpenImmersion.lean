module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.DifferentialsRestrict.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap

/-!
# Relative differentials restricted to an open of the source

The canonical morphism `f^* Ω_{X/S} ⟶ Ω_{X'/S'}` of Stacks 01UV attached to a commutative square
of schemes is an isomorphism as soon as its upper edge `f` is an open immersion and its lower
edge is an isomorphism: the sheaf of relative differentials of a morphism restricted to an open
of its source is the sheaf of relative differentials of the restricted morphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativeDifferentialsMap_id` and
  `AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap.comp`: the identity is a map of
  relative differentials, and maps of relative differentials compose.
* `AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap.congr_left`: a map of relative
  differentials for a morphism is one for any equal morphism.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isIso`: the canonical morphism
  of a square whose horizontal edges are isomorphisms is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isOpenImmersion`: the canonical
  morphism of a square whose upper edge is an open immersion and whose lower edge is an
  isomorphism is an isomorphism.

## References

* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local simp] Scheme.Modules.pseudofunctor_associativity
  Scheme.Modules.pseudofunctor_left_unitality
  Scheme.Modules.pseudofunctor_right_unitality
  CategoryTheory.Bicategory.toNatTrans_conjugateEquiv
  CategoryTheory.unit_conjugateEquiv
  Scheme.Modules.conjugateEquiv_pullbackId_hom
  CategoryTheory.Bicategory.Adjunction.ofCat_comp
  Scheme.Modules.conjugateEquiv_pullbackComp_inv

/-- The identity of `X` is a map of relative differentials from `Ω_{X/S}` to itself. -/
theorem isRelativeDifferentialsMap_id {X S : Scheme.{u}} (p : X ⟶ S) :
    IsRelativeDifferentialsMap (𝟙 X) p p
      ((Scheme.Modules.pullbackId X).hom.app (relativeDifferentials p)) := by
  intro U h
  rw [Adjunction.homEquiv_unit, pullbackId_unit (relativeDifferentials p)]
  change (Scheme.Modules.Hom.app
      ((Scheme.Modules.pushforwardId X).inv.app (relativeDifferentials p)) U)
    ((universalRelativeDerivation p).d h) = _
  rw [Scheme.Modules.pushforwardId_inv_app_app]
  rfl

/-- A map of relative differentials for one morphism is one for any equal morphism, transported
along `AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
theorem IsRelativeDifferentialsMap.congr_left {X' X S' S : Scheme.{u}} {f f₁ : X' ⟶ X}
    {p : X ⟶ S} {p' : X' ⟶ S'}
    {c : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶ relativeDifferentials p'}
    (hc : IsRelativeDifferentialsMap f p p' c) (h : f = f₁) :
    IsRelativeDifferentialsMap f₁ p p'
      ((Scheme.Modules.pullbackCongr h).inv.app (relativeDifferentials p) ≫ c) := by
  subst h
  convert hc using 1
  exact Category.id_comp c

/-- **Maps of relative differentials compose**, for arbitrary bases `S`, `S'` and `S''`. -/
theorem IsRelativeDifferentialsMap.comp {X'' X' X S'' S' S : Scheme.{u}}
    {f : X' ⟶ X} {f' : X'' ⟶ X'} {p : X ⟶ S} {p' : X' ⟶ S'} {p'' : X'' ⟶ S''}
    {c : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶ relativeDifferentials p'}
    {c' : (Scheme.Modules.pullback f').obj (relativeDifferentials p') ⟶ relativeDifferentials p''}
    (hc : IsRelativeDifferentialsMap f p p' c)
    (hc' : IsRelativeDifferentialsMap f' p' p'' c') :
    IsRelativeDifferentialsMap (f' ≫ f) p p''
      ((Scheme.Modules.pullbackComp f' f).inv.app (relativeDifferentials p) ≫
        (Scheme.Modules.pullback f').map c ≫ c') := by
  let M := relativeDifferentials p
  let N := relativeDifferentials p'
  let P := relativeDifferentials p''
  let adjF := Scheme.Modules.pullbackPushforwardAdjunction f'
  let adjG := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjFG := Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ f)
  let d : (Scheme.Modules.pullback (f' ≫ f)).obj M ⟶ P :=
    (Scheme.Modules.pullbackComp f' f).inv.app M ≫ (Scheme.Modules.pullback f').map c ≫ c'
  have hAdj : adjFG.homEquiv M P d =
      adjG.homEquiv M N c ≫
        (Scheme.Modules.pushforward f).map (adjF.homEquiv N P c') ≫
        (Scheme.Modules.pushforwardComp f' f).hom.app P := by
    dsimp [adjFG, adjG, adjF, d]
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_comp, ← Category.assoc, pullbackComp_unit f' f M]
    simp only [Category.assoc]
    have hn := (Scheme.Modules.pushforwardComp f' f).hom.naturality
      ((Scheme.Modules.pullback f').map c ≫ c')
    simp only [Functor.comp_map] at hn
    rw [← hn]
    have hfN := (Scheme.Modules.pullbackPushforwardAdjunction f').unit.naturality c
    simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hfN
    have hsection : (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
          ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback f').map c ≫ c') =
      c ≫ (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app N ≫
        (Scheme.Modules.pushforward f').map c' := by
      rw [Functor.map_comp, ← Category.assoc, ← hfN]
      exact Category.assoc _ _ _
    calc
      _ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
          (Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
                ((Scheme.Modules.pullback f).obj M) ≫
              (Scheme.Modules.pushforward f').map
                ((Scheme.Modules.pullback f').map c ≫ c')) ≫
          (Scheme.Modules.pushforwardComp f' f).hom.app P := by
        rw [(Scheme.Modules.pushforward f).map_comp]
        cat_disch
      _ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
          (Scheme.Modules.pushforward f).map
            (c ≫ (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app N ≫
              (Scheme.Modules.pushforward f').map c') ≫
          (Scheme.Modules.pushforwardComp f' f).hom.app P := by
        rw [hsection]
      _ = _ := by
        rw [(Scheme.Modules.pushforward f).map_comp]
        cat_disch
  intro U h
  let V := f ⁻¹ᵁ U
  let dZ := universalRelativeDerivation p
  let dY := universalRelativeDerivation p'
  let dX := universalRelativeDerivation p''
  have hEval := congrArg
    (fun a : M ⟶ (Scheme.Modules.pushforward (f' ≫ f)).obj P => a.app U (dZ.d h)) hAdj
  change (Scheme.Modules.Hom.app (adjFG.homEquiv M P d) U) (dZ.d h) = _
  rw [hEval]
  simp only [Scheme.Modules.pushforward_obj_obj, Scheme.Hom.comp_base, Opens.map_comp_obj,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Functor.comp_obj,
    Scheme.Hom.comp_app, CommRingCat.hom_comp]
  have hgU' : (Scheme.Modules.Hom.app (adjG.homEquiv M N c) U) (dZ.d h) =
      dY.d ((f.app U).hom h) := hc U h
  have hfV' : (Scheme.Modules.Hom.app (adjF.homEquiv N P c') V)
      (dY.d ((f.app U).hom h)) =
      dX.d ((f'.app V).hom ((f.app U).hom h)) := hc' V ((f.app U).hom h)
  change (Scheme.Modules.Hom.app (adjF.homEquiv N P c') V)
      ((Scheme.Modules.Hom.app (adjG.homEquiv M N c) U) (dZ.d h)) = _
  rw [hgU', hfV']
  rfl

/-- A morphism with an isomorphism on each side is itself an isomorphism. -/
private theorem isIso_of_isIso_comp_both {C : Type*} [Category* C] {A B D E : C}
    (w : A ⟶ B) (u : B ⟶ D) (c : D ⟶ E) [IsIso (w ≫ u)] [IsIso (u ≫ c)] : IsIso u := by
  have : IsSplitMono u := .mk' ⟨c ≫ inv (u ≫ c), by rw [← Category.assoc]; simp⟩
  have : IsSplitEpi u := .mk' ⟨inv (w ≫ u) ≫ w, by rw [Category.assoc]; simp⟩
  exact isIso_of_mono_of_isSplitEpi u

/-- If `a ≫ b = 𝟙 X` and `c`, `d` are maps of relative differentials for `b` and `a`, then
`a^* c ≫ d` is an isomorphism. -/
private theorem isIso_pullback_map_comp_of_comp_eq_id {X' X S' S : Scheme.{u}} {a : X ⟶ X'}
    {b : X' ⟶ X} (hab : a ≫ b = 𝟙 X) {p : X ⟶ S} {p' : X' ⟶ S'}
    {c : (Scheme.Modules.pullback b).obj (relativeDifferentials p) ⟶ relativeDifferentials p'}
    {d : (Scheme.Modules.pullback a).obj (relativeDifferentials p') ⟶ relativeDifferentials p}
    (hc : IsRelativeDifferentialsMap b p p' c) (hd : IsRelativeDifferentialsMap a p' p d) :
    IsIso ((Scheme.Modules.pullback a).map c ≫ d) := by
  have e := ((hc.comp hd).congr_left hab).unique (𝟙 S) (by simp)
    (isRelativeDifferentialsMap_id p)
  have key : (Scheme.Modules.pullback a).map c ≫ d =
      (Scheme.Modules.pullbackComp a b).hom.app (relativeDifferentials p) ≫
        (Scheme.Modules.pullbackCongr hab).hom.app (relativeDifferentials p) ≫
        (Scheme.Modules.pullbackId X).hom.app (relativeDifferentials p) := by
    rw [← e]; simp
  rw [key]; infer_instance

/-- **The canonical map on relative differentials of a square whose horizontal edges are
isomorphisms is an isomorphism.** -/
theorem isIso_relativeDifferentialsMap_of_isIso {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g)
    [IsIso f] [IsIso g] : IsIso (relativeDifferentialsMap f p p' g hcomm) := by
  have hcomm' : inv f ≫ p' = p ≫ inv g := by
    rw [← cancel_epi f, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
      ← Category.assoc, hcomm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  set c := relativeDifferentialsMap f p p' g hcomm
  set d := relativeDifferentialsMap (inv f) p' p (inv g) hcomm'
  have hc : IsRelativeDifferentialsMap f p p' c :=
    isRelativeDifferentialsMap_relativeDifferentialsMap f p p' g hcomm
  have hd : IsRelativeDifferentialsMap (inv f) p' p d :=
    isRelativeDifferentialsMap_relativeDifferentialsMap (inv f) p' p (inv g) hcomm'
  have hv := isIso_pullback_map_comp_of_comp_eq_id (IsIso.inv_hom_id f) hc hd
  have hu := isIso_pullback_map_comp_of_comp_eq_id (IsIso.hom_inv_id f) hd hc
  have hw : IsIso ((Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullback (inv f)).map c) ≫ (Scheme.Modules.pullback f).map d) := by
    rw [← Functor.map_comp]; infer_instance
  have hud : IsIso ((Scheme.Modules.pullback f).map d) :=
    isIso_of_isIso_comp_both
      ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback (inv f)).map c))
      ((Scheme.Modules.pullback f).map d) c
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.pullback f).map d) c

/-- A composite of two canonical maps on relative differentials, each an isomorphism, is the
canonical map of the composite square, so that one is an isomorphism too. -/
private theorem isIso_relativeDifferentialsMap_of_comp
    {X'' X' X S'' S' S : Scheme.{u}} {f : X' ⟶ X} {f' : X'' ⟶ X'} {k : X'' ⟶ X}
    (hk : f' ≫ f = k) {p : X ⟶ S} {p' : X' ⟶ S'} {p'' : X'' ⟶ S''}
    (g : S' ⟶ S) (h : f ≫ p = p' ≫ g) (g' : S'' ⟶ S') (h' : f' ≫ p' = p'' ≫ g')
    (g'' : S'' ⟶ S) (h'' : k ≫ p = p'' ≫ g'')
    [IsIso (relativeDifferentialsMap f p p' g h)]
    [IsIso (relativeDifferentialsMap f' p' p'' g' h')] :
    IsIso (relativeDifferentialsMap k p p'' g'' h'') := by
  have h1 := isRelativeDifferentialsMap_relativeDifferentialsMap f p p' g h
  have h2 := isRelativeDifferentialsMap_relativeDifferentialsMap f' p' p'' g' h'
  have h3 := (h1.comp h2).congr_left hk
  rw [← h3.eq_relativeDifferentialsMap g'' h'']
  infer_instance

/-- The inclusion of the top open of a scheme is an isomorphism. -/
private instance isIso_ι_top (S : Scheme.{u}) : IsIso ((⊤ : S.Opens).ι) :=
  inferInstanceAs (IsIso S.topIso.hom)

/-- The canonical map `(U ↪ X)^* Ω_{X/S} ⟶ Ω_{U/S}` of an open subscheme of the source is an
isomorphism. -/
private theorem isIso_relativeDifferentialsMap_ι {X S : Scheme.{u}} (p : X ⟶ S) (U : X.Opens) :
    IsIso (relativeDifferentialsMap U.ι p (U.ι ≫ p) (𝟙 S) (by simp)) := by
  have hsquare : U.ι ≫ p = p.resLE ⊤ U le_top ≫ (⊤ : S.Opens).ι :=
    Stacks.AlgebraicGeometry.DifferentialsRestrict.resLE_square p ⊤ U le_top
  have h0 : IsIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
      (relativeDifferentials p) ≫
      relativeDifferentialsMap U.ι p (p.resLE ⊤ U le_top) (⊤ : S.Opens).ι hsquare) :=
    inferInstanceAs
      (IsIso (Stacks.AlgebraicGeometry.DifferentialsRestrict.restrictIso p ⊤ U le_top).hom)
  have hres : IsIso (relativeDifferentialsMap U.ι p (p.resLE ⊤ U le_top)
      (⊤ : S.Opens).ι hsquare) :=
    IsIso.of_isIso_comp_left
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app (relativeDifferentials p)) _
  have hsq : 𝟙 U.toScheme ≫ p.resLE ⊤ U le_top = (U.ι ≫ p) ≫ inv (⊤ : S.Opens).ι := by
    rw [Category.id_comp, hsquare, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hbase : IsIso (relativeDifferentialsMap (𝟙 U.toScheme) (p.resLE ⊤ U le_top)
      (U.ι ≫ p) (inv (⊤ : S.Opens).ι) hsq) :=
    isIso_relativeDifferentialsMap_of_isIso _ _ _ _ hsq
  exact isIso_relativeDifferentialsMap_of_comp (Category.id_comp U.ι)
    (⊤ : S.Opens).ι hsquare (inv (⊤ : S.Opens).ι) hsq (𝟙 S) (by simp)

/-- **The canonical map on relative differentials of a square whose upper edge is an open
immersion and whose lower edge is an isomorphism is an isomorphism**: the sheaf of relative
differentials of a morphism restricted to an open of its source is the restriction of the sheaf
of relative differentials. -/
theorem isIso_relativeDifferentialsMap_of_isOpenImmersion {X' X S' S : Scheme.{u}}
    (j : X' ⟶ X) [IsOpenImmersion j] (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
    (hcomm : j ≫ p = p' ≫ g) [IsIso g] :
    IsIso (relativeDifferentialsMap j p p' g hcomm) := by
  set U := j.opensRange
  have hrange : Set.range j.base = Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rfl
  set ε := IsOpenImmersion.isoOfRangeEq j U.ι hrange
  have hfac : ε.hom ≫ U.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac j U.ι hrange
  have hι : IsIso (relativeDifferentialsMap U.ι p (U.ι ≫ p) (𝟙 S) (by simp)) :=
    isIso_relativeDifferentialsMap_ι p U
  have hsq : ε.hom ≫ (U.ι ≫ p) = (j ≫ p) ≫ 𝟙 S := by
    rw [Category.comp_id, ← Category.assoc, hfac]
  have hε' : IsIso (relativeDifferentialsMap ε.hom (U.ι ≫ p) (j ≫ p) (𝟙 S) hsq) :=
    isIso_relativeDifferentialsMap_of_isIso _ _ _ _ hsq
  have hj : IsIso (relativeDifferentialsMap j p (j ≫ p) (𝟙 S) (by simp)) :=
    isIso_relativeDifferentialsMap_of_comp hfac (𝟙 S) (Category.comp_id _).symm (𝟙 S) hsq (𝟙 S)
      (by simp)
  have hsq2 : 𝟙 X' ≫ (j ≫ p) = p' ≫ g := by rw [Category.id_comp, hcomm]
  have hlast : IsIso (relativeDifferentialsMap (𝟙 X') (j ≫ p) p' g hsq2) :=
    isIso_relativeDifferentialsMap_of_isIso _ _ _ _ hsq2
  exact isIso_relativeDifferentialsMap_of_comp (Category.id_comp j) (𝟙 S)
    (Category.comp_id _).symm g hsq2 g hcomm

/-- The open-immersion case of
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isOpenImmersion` over a fixed
base, as an instance. -/
instance isIso_relativeDifferentialsMap_id_base {X' X S : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (p : X ⟶ S) (p' : X' ⟶ S) (hcomm : j ≫ p = p' ≫ 𝟙 S) :
    IsIso (relativeDifferentialsMap j p p' (𝟙 S) hcomm) :=
  isIso_relativeDifferentialsMap_of_isOpenImmersion j p p' (𝟙 S) hcomm

end AlgebraicGeometry.Scheme.Hom

end
