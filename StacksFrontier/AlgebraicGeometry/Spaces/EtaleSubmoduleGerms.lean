module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionFiber
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# Germs of submodules along étale morphisms of algebraic spaces

Let `g : Y ⟶ X` be an étale morphism of algebraic spaces, `M` an `𝒪_X`-module and `N` a
submodule of the étale pullback `M|_Y`.  For a geometric point `x̄` of `X` and a lift `t` of `x̄`
to `Y`, this file considers the set of germs at `x̄` — in the fibre of the sheaf of sets
underlying `M` at the point of the small étale site of `X` attached to `x̄` — of the sections of
`N` over the charts of `Y`, taken at the lifts of `t`.  Two facts make these germ sets useful.

* **They detect membership**: a section of `M|_Y` over a chart of `Y` lies in `N` as soon as its
  germ at every lift of every geometric point lies in the corresponding germ set
  (`AlgebraicGeometry.Space.mem_of_forall_germ_mem_etaleGermSet`).  This is where Stacks'
  Equation 08GT enters: the fibre of `M|_Y` at a lift is the fibre of `M` at the point, so an
  equality of germs of `M` is an equality of germs of `M|_Y`.
* **They are insensitive to a further étale restriction**
  (`AlgebraicGeometry.Space.etaleGermSet_along`): for `h : Y' ⟶ Y` étale, the germ set of the
  restriction of `N` along `h` at a lift of `t` to `Y'` is the germ set of `N` at `t`.

Together they reduce a compatibility of submodules across chart morphisms to an equality of germ
sets at each geometric point.

## Main definitions

* `AlgebraicGeometry.Space.etaleGermSet`: the germ set of `N` at a lift.

## Main results

* `AlgebraicGeometry.Space.mem_of_forall_germ_mem`: membership in a submodule is detected by
  germs at the geometric points of the space.
* `AlgebraicGeometry.Space.mem_of_forall_germ_mem_etaleGermSet`: membership in `N` is detected by
  the germ sets.
* `AlgebraicGeometry.Space.etaleGermSet_along`: the germ sets are insensitive to a further étale
  restriction.

## References

* [Stacks Project, Tag 08GT](https://stacks.math.columbia.edu/tag/08GT)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf of sets underlying an `𝒪_X`-module, as a presheaf of types on the small étale
site. -/
abbrev etaleModuleSectionsPresheaf {X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u :=
  M.val.presheaf ⋙ forget AddCommGrpCat.{u}

/-- **Membership in a submodule is detected at the geometric points.**  A section `s` of an
`𝒪_X`-module over a chart `V` lies in a submodule `N` as soon as every lift of every geometric
point of `X` to `V` has a neighbourhood over which `s` restricts into `N`. -/
theorem mem_of_forall_germ_mem {X : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS X.1 X.2}
    (N : M.Submodule) (V : SmallEtale B S hS X.1) (s : M.val.obj (op V))
    (h : ∀ (y : GeometricPoint B S hS X.1) (p : (etaleSitePoint B S hS X.1 y X.2).fiber.obj V),
      ∃ (V' : SmallEtale B S hS X.1) (ψ : V' ⟶ V)
        (p' : (etaleSitePoint B S hS X.1 y X.2).fiber.obj V'),
        (etaleSitePoint B S hS X.1 y X.2).fiber.map ψ p' = p ∧
          M.val.map ψ.op s ∈ N.obj (op V')) :
    s ∈ N.obj (op V) := by
  refine N.isSheaf (X := op V) s ?_
  refine smallEtale_sieve_of_pointwise_covering B S hS X.1 V _ fun z => ?_
  obtain ⟨y, p, z', hz'⟩ := exists_geo_lift_at_chart_point B S hS X.1 V z
  obtain ⟨V', ψ, p', hp', hmem⟩ := h y p
  refine ⟨V', ψ, hmem, (BigFppfOver.toScheme B S hS).map p'.1 z', ?_⟩
  rw [← hz', ← hp']
  show _ = (BigFppfOver.toScheme B S hS).map (p'.1 ≫ (SmallEtale.toOver B S hS X.1).map ψ) z'
  rw [Functor.map_comp]
  rfl

section GermSet

variable {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
  {M : Modules.{u, u} B S hS X.1 X.2}

/-- **The germ set of a submodule of `M|_Y` at a lift.**  For a geometric point `x̄` of `X` and a
lift `t` of `x̄` to `Y`, the germs at `x̄` of the sections of `N` over the charts `V` of `Y`, taken
at the lifts of `t` to `V`. -/
def etaleGermSet (N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x) :
    Set ((etaleSitePoint B S hS X.1 x X.2).presheafFiber.obj
      (etaleModuleSectionsPresheaf B S hS M)) :=
  {e | ∃ (V : SmallEtale B S hS Y.1) (w : (liftSitePoint B S hS g t).fiber.obj V)
    (n : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V))),
      n ∈ N.obj (op V) ∧
        (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber ((smallEtalePostcomp B S hS g hg).obj V)
          (pushLift B S hS g hg V t w) (etaleModuleSectionsPresheaf B S hS M) n = e}

/-- The germ of a section of `N` at a lift lies in the germ set. -/
theorem germ_mem_etaleGermSet (N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    (V : SmallEtale B S hS Y.1) (w : (liftSitePoint B S hS g t).fiber.obj V)
    (n : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V))) (hn : n ∈ N.obj (op V)) :
    (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber ((smallEtalePostcomp B S hS g hg).obj V)
      (pushLift B S hS g hg V t w) (etaleModuleSectionsPresheaf B S hS M) n ∈
        etaleGermSet B S hS g hg N t :=
  ⟨V, w, n, hn, rfl⟩

/-- Stacks' Equation 08GT on elements: the comparison isomorphism carries the germ of a section
at a lift to its germ at the geometric point. -/
theorem restrictionPresheafFiberIso_hom_toPresheafFiber_apply
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    (P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (Z : SmallEtale B S hS Y.1)
    (z : (liftSitePoint B S hS g t).fiber.obj Z)
    (a : P.obj (op ((smallEtalePostcomp B S hS g hg).obj Z))) :
    ((restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app P).hom
        ((liftSitePoint B S hS g t).toPresheafFiber Z z
          ((smallEtalePostcomp B S hS g hg).op ⋙ P) a) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber
        ((smallEtalePostcomp B S hS g hg).obj Z) (pushLift B S hS g hg Z t z) P a := by
  have := ConcreteCategory.congr_hom
    (restrictionPresheafFiberIso_toPresheafFiber (A := Type u) B S hS g hg t P Z z) a
  rwa [ConcreteCategory.comp_apply] at this

/-- A germ at `x̄` of a section of a subpresheaf is the germ, at `x̄`, of a section over a chart
coming from `Y` at a lift `t`, by Stacks' Equation 08GT applied to the subpresheaf. -/
private theorem exists_toPresheafFiber_pushLift_eq
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    {Q P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u} (ι : Q ⟶ P) (V : SmallEtale B S hS X.1)
    (w : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V) (q : Q.obj (op V)) :
    ∃ (V' : SmallEtale B S hS Y.1) (w' : (liftSitePoint B S hS g t).fiber.obj V')
      (m : Q.obj (op ((smallEtalePostcomp B S hS g hg).obj V'))),
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber ((smallEtalePostcomp B S hS g hg).obj V')
        (pushLift B S hS g hg V' t w') P (ι.app _ m) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber V w P (ι.app _ q) := by
  let ιg := (restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app Q
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso ιg.hom).2
    ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber V w Q q)
  obtain ⟨V', w', m, rfl⟩ := (liftSitePoint B S hS g t).toPresheafFiber_jointly_surjective
    (P := (smallEtalePostcomp B S hS g hg).op ⋙ Q) r
  have h1 := restrictionPresheafFiberIso_hom_toPresheafFiber_apply B S hS g hg t Q V' w' m
  have h2 := congrArg ((etaleSitePoint B S hS X.1 x X.2).presheafFiber.map ι) (h1.symm.trans hr)
  have hn1 := (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_naturality_apply ι
    ((smallEtalePostcomp B S hS g hg).obj V') (pushLift B S hS g hg V' t w') m
  have hn2 := (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_naturality_apply ι V w q
  exact ⟨V', w', m, hn1.symm.trans (h2.trans hn2)⟩

/-- **Membership in `N` is detected by the germ sets.**  A section of `M|_Y` over a chart `V` of
`Y` whose germ at every lift of every geometric point of `X` lies in the germ set of `N` at that
lift is a section of `N`.

The germ of `s` at a lift agrees with the germ of a section of `N`; by Stacks' Equation 08GT,
`AlgebraicGeometry.Space.restrictionPresheafFiberIso`, the two germs then agree already in the
fibre of `M|_Y`, hence over a neighbourhood of the lift, and
`AlgebraicGeometry.Space.mem_of_forall_germ_mem` concludes. -/
theorem mem_of_forall_germ_mem_etaleGermSet
    (N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule) (V : SmallEtale B S hS Y.1)
    (s : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V)))
    (h : ∀ (x : GeometricPoint B S hS X.1) (t : GeometricPointLift B S hS g.hom x)
      (w : (liftSitePoint B S hS g t).fiber.obj V),
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber ((smallEtalePostcomp B S hS g hg).obj V)
        (pushLift B S hS g hg V t w) (etaleModuleSectionsPresheaf B S hS M) s ∈
          etaleGermSet B S hS g hg N t) :
    s ∈ N.obj (op V) := by
  refine mem_of_forall_germ_mem B S hS N V s fun y p => ?_
  let x : GeometricPoint B S hS X.1 := geometricPointMap g.hom y
  let t : GeometricPointLift B S hS g.hom x := ⟨y.val.value, rfl⟩
  let Φ := liftSitePoint B S hS g t
  let P := etaleModuleSectionsPresheaf B S hS M
  let w : Φ.fiber.obj V := p
  obtain ⟨V', w', n, hn, he⟩ := h x t w
  have hι := restrictionPresheafFiberIso_hom_toPresheafFiber_apply B S hS g hg t P
  have heq : Φ.toPresheafFiber V w ((smallEtalePostcomp B S hS g hg).op ⋙ P) s =
      Φ.toPresheafFiber V' w' ((smallEtalePostcomp B S hS g hg).op ⋙ P) n :=
    (ConcreteCategory.bijective_of_isIso
      ((restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app P).hom).1
      ((hι V w s).trans (he.symm.trans (hι V' w' n).symm))
  obtain ⟨E₀, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs
    (C := Φ.fiber.Elements) (Φ.fiber.elementsMk V w) (Φ.fiber.elementsMk V' w')
  have ha := Φ.toPresheafFiber_w_apply a.hom E₀.val ((smallEtalePostcomp B S hS g hg).op ⋙ P) s
  have hb := Φ.toPresheafFiber_w_apply b.hom E₀.val ((smallEtalePostcomp B S hS g hg).op ⋙ P) n
  rw [a.map_val] at ha
  rw [b.map_val] at hb
  rw [← ha, ← hb] at heq
  obtain ⟨V₁, c, w₁, hc, hcs⟩ := (Φ.toPresheafFiber_eq_iff' E₀.obj E₀.val _ _).1 heq
  refine ⟨V₁, c ≫ a.hom, w₁, ?_, ?_⟩
  · show Φ.fiber.map (c ≫ a.hom) w₁ = w
    rw [Functor.map_comp, types_comp_apply, hc, a.map_val]
  · have e : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map (c ≫ a.hom).op s =
        ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map (c ≫ b.hom).op n := by
      simp only [Functor.comp_map] at hcs
      let MY := ((etaleModulePullback.{u, u} B S hS g hg).obj M).val
      exact (PresheafOfModules.map_comp_apply MY a.hom.op c.op s).trans
        (hcs.trans (PresheafOfModules.map_comp_apply MY b.hom.op c.op n).symm)
    rw [e]
    exact N.map_mem (c ≫ b.hom).op hn

/-- A lift `t'` along `k : Y' ⟶ Y` of the geometric point attached to a lift `t` along `g` is a
lift along the composite `k ≫ g`. -/
def GeometricPointLift.comp {Y' : AlgebraicSpaces B S hS} (k : Y' ⟶ Y)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    (t' : GeometricPointLift B S hS k.hom (liftGeometricPoint B S hS g t)) :
    GeometricPointLift B S hS (k ≫ g).hom x :=
  ⟨t'.1, by
    change g.hom.app _ (k.hom.app _ t'.1) = _
    rw [t'.2]
    exact t.2⟩

/-- **The germ sets are insensitive to a further étale restriction.**  For étale `k : Y' ⟶ Y`, the
germ set of the restriction of `N` along `k` at a lift `t'` to `Y'` of the point attached to `t`
is the germ set of `N` at `t`.

One inclusion is a reindexing.  For the other, a germ of a section of `N` at `t` is, by Stacks'
Equation 08GT for `k` applied to the sheaf of sets underlying `N`, the germ of a section of `N`
over a chart coming from `Y'`. -/
theorem etaleGermSet_along {Y' : AlgebraicSpaces B S hS} (k : Y' ⟶ Y)
    (hk : IsEtale B S hS k.hom) (hkg : IsEtale B S hS (k ≫ g).hom)
    (N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    (t' : GeometricPointLift B S hS k.hom (liftGeometricPoint B S hS g t)) :
    etaleGermSet B S hS (k ≫ g) hkg (etaleSubmoduleAlong B S hS k hk g hg hkg N)
        (GeometricPointLift.comp B S hS g k t t') =
      etaleGermSet B S hS g hg N t := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro e ⟨V', w', n, hn, rfl⟩
    refine ⟨(smallEtalePostcomp B S hS k hk).obj V', ⟨w'.1, ?_⟩, n, hn, rfl⟩
    show k.hom.app _ (V'.obj.hom.app _ w'.1) = t.1
    have := w'.2
    change V'.obj.hom.app _ w'.1 = t'.1 at this
    rw [this]
    exact t'.2
  · rintro e ⟨V, w, n, hn, rfl⟩
    let ΦY := liftSitePoint B S hS g t
    obtain ⟨V', w', m, h2'⟩ := exists_toPresheafFiber_pushLift_eq B S hS k hk t'
      N.toSubfunctor.ι V w ⟨n, hn⟩
    let P := etaleModuleSectionsPresheaf B S hS M
    let ιg := (restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app P
    have h3 := congrArg ιg.hom h2'
    have hg1 : ιg.hom (ΦY.toPresheafFiber ((smallEtalePostcomp B S hS k hk).obj V')
          (pushLift B S hS k hk V' t' w') ((smallEtalePostcomp B S hS g hg).op ⋙ P) m.1) = _ :=
      restrictionPresheafFiberIso_hom_toPresheafFiber_apply B S hS g hg t P _
        (pushLift B S hS k hk V' t' w') m.1
    exact ⟨V', w', m.1, m.2, hg1.symm.trans (h3.trans
      (restrictionPresheafFiberIso_hom_toPresheafFiber_apply B S hS g hg t P V w n))⟩

/-- **Two submodules of `M|_Y` with the same germ sets at every lift are equal.** -/
theorem etaleSubmodule_ext_of_etaleGermSet
    {N N' : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule}
    (h : ∀ (x : GeometricPoint B S hS X.1) (t : GeometricPointLift B S hS g.hom x),
      etaleGermSet B S hS g hg N t = etaleGermSet B S hS g hg N' t) : N = N' := by
  have key : ∀ {N₁ N₂ : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule},
      (∀ (x : GeometricPoint B S hS X.1) (t : GeometricPointLift B S hS g.hom x),
        etaleGermSet B S hS g hg N₁ t ⊆ etaleGermSet B S hS g hg N₂ t) → N₁ ≤ N₂ := by
    intro N₁ N₂ h12 V s hs
    exact mem_of_forall_germ_mem_etaleGermSet B S hS g hg N₂ V.unop s fun x t w =>
      h12 x t (germ_mem_etaleGermSet B S hS g hg N₁ t V.unop w s hs)
  exact le_antisymm (key fun x t => (h x t).le) (key fun x t => (h x t).ge)

/-- **Germ-set containment gives restriction along chart morphisms.**  Let `N ⊆ M|_Y` and
`N' ⊆ M|_{Y'}` for étale `g : Y ⟶ X` and `g' : Y' ⟶ X`.  If at every geometric point of `X` the
germ set of `N'` at any lift is contained in the germ set of `N` at any lift, then restriction
along any morphism of charts of `X` from a chart of `Y` to a chart of `Y'` carries the sections of
`N'` into those of `N`. -/
theorem map_mem_of_etaleGermSet_subset {Y' : AlgebraicSpaces B S hS} (g' : Y' ⟶ X)
    (hg' : IsEtale B S hS g'.hom)
    (N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    (N' : ((etaleModulePullback.{u, u} B S hS g' hg').obj M).Submodule)
    (h : ∀ (x : GeometricPoint B S hS X.1) (t : GeometricPointLift B S hS g.hom x)
      (t' : GeometricPointLift B S hS g'.hom x),
      etaleGermSet B S hS g' hg' N' t' ⊆ etaleGermSet B S hS g hg N t)
    (V : SmallEtale B S hS Y.1) (V' : SmallEtale B S hS Y'.1)
    (φ : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g' hg').obj V')
    (n : M.val.obj (op ((smallEtalePostcomp B S hS g' hg').obj V'))) (hn : n ∈ N'.obj (op V')) :
    M.val.map φ.op n ∈ N.obj (op V) := by
  refine mem_of_forall_germ_mem_etaleGermSet B S hS g hg N V _ fun x t w => ?_
  let a := (etaleSitePoint B S hS X.1 x X.2).fiber.map φ (pushLift B S hS g hg V t w)
  have ha : (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber
      ((smallEtalePostcomp B S hS g hg).obj V) (pushLift B S hS g hg V t w)
      (etaleModuleSectionsPresheaf B S hS M) (M.val.map φ.op n) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber
        ((smallEtalePostcomp B S hS g' hg').obj V') a (etaleModuleSectionsPresheaf B S hS M) n :=
    (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_w_apply φ (pushLift B S hS g hg V t w)
      (etaleModuleSectionsPresheaf B S hS M) n
  rw [ha]
  let t' : GeometricPointLift B S hS g'.hom x := ⟨V'.obj.hom.app _ a.1, a.2⟩
  let w' : (liftSitePoint B S hS g' t').fiber.obj V' := ⟨a.1, rfl⟩
  exact h x t t' (germ_mem_etaleGermSet B S hS g' hg' N' t' V' w' n hn)

/-- **The germ set of a submodule of `M` at a geometric point**: the germs of its sections. -/
def submoduleGermSet (K : M.Submodule) (x : GeometricPoint B S hS X.1) :
    Set ((etaleSitePoint B S hS X.1 x X.2).presheafFiber.obj
      (etaleModuleSectionsPresheaf B S hS M)) :=
  {e | ∃ (V : SmallEtale B S hS X.1) (w : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V)
    (n : M.val.obj (op V)), n ∈ K.obj (op V) ∧
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber V w
        (etaleModuleSectionsPresheaf B S hS M) n = e}

/-- **The germ set of the restriction of a submodule at any lift is its germ set at the point.**
One inclusion is a reindexing; the other is Stacks' Equation 08GT for `g` applied to the sheaf of
sets underlying the submodule. -/
theorem etaleGermSet_etaleSubmoduleRestrict (K : M.Submodule) {x : GeometricPoint B S hS X.1}
    (t : GeometricPointLift B S hS g.hom x) :
    etaleGermSet B S hS g hg (etaleSubmoduleRestrict B S hS g hg K) t =
      submoduleGermSet B S hS K x := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro e ⟨V, w, n, hn, rfl⟩
    exact ⟨_, _, n, hn, rfl⟩
  · rintro e ⟨V, w, n, hn, rfl⟩
    obtain ⟨V', w', m, hm⟩ := exists_toPresheafFiber_pushLift_eq B S hS g hg t
      K.toSubfunctor.ι V w ⟨n, hn⟩
    exact ⟨V', w', m.1, m.2, hm⟩

/-- Germ sets are unchanged by transport along an equality of étale morphisms. -/
theorem etaleGermSet_etaleSubmoduleCongr {a b : Y ⟶ X} (hab : a = b)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (N : ((etaleModulePullback.{u, u} B S hS a ha).obj M).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS a.hom x)
    (t' : GeometricPointLift B S hS b.hom x) (htt : t.1 = t'.1) :
    etaleGermSet B S hS b hb (etaleSubmoduleCongr B S hS hab ha hb N) t' =
      etaleGermSet B S hS a ha N t := by
  subst hab
  obtain rfl : t = t' := Subtype.ext htt
  rfl

/-- **Germ sets of an iterated restriction.**  For étale `k : Y' ⟶ Y` and a submodule `N` of
`(M|_Y)|_{Y'}`, the comparison of Stacks' Equation 08GT for `g` at a lift `t` carries the germ set
of `N` at a lift `t'` of the point attached to `t` onto the germ set of `N`, read along the
composite `k ≫ g`, at the composite lift. -/
theorem image_etaleGermSet_iter {Y' : AlgebraicSpaces B S hS} (k : Y' ⟶ Y)
    (hk : IsEtale B S hS k.hom) (hkg : IsEtale B S hS (k ≫ g).hom)
    (N : ((etaleModulePullback.{u, u} B S hS k hk).obj
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    (t' : GeometricPointLift B S hS k.hom (liftGeometricPoint B S hS g t)) :
    ((restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app
        (etaleModuleSectionsPresheaf B S hS M)).hom ''
        etaleGermSet B S hS k hk N t' =
      etaleGermSet B S hS (k ≫ g) hkg (etaleSubmoduleIterToComp B S hS k hk g hg hkg N)
        (GeometricPointLift.comp B S hS g k t t') := by
  have hι := restrictionPresheafFiberIso_hom_toPresheafFiber_apply B S hS g hg t
    (etaleModuleSectionsPresheaf B S hS M)
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro e ⟨_, ⟨V, w, n, hn, rfl⟩, rfl⟩
    exact ⟨V, ⟨w.1, w.2⟩, n, hn, (hι _ (pushLift B S hS k hk V t' w) n).symm⟩
  · rintro e ⟨V, w, n, hn, rfl⟩
    let w₀ : (liftSitePoint B S hS k t').fiber.obj V := ⟨w.1, w.2⟩
    exact ⟨_, ⟨V, w₀, n, hn, rfl⟩, hι _ (pushLift B S hS k hk V t' w₀) n⟩

end GermSet

end AlgebraicGeometry.Space

end
