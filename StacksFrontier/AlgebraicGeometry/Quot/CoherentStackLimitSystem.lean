module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitsInSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Systems of base changes along a cofiltered limit of affine schemes

Artin's Axioms, Definition 07XL, quantifies over cofiltered inverse systems `T_j` of affine
schemes of the big fppf site whose limit `T` in schemes is again an object of the site. This
file records the two facts about such systems which the proof of Stacks 08KD uses, in the
vocabulary of the descent results on limits of algebraic spaces:

* the system of representable presheaves `j ↦ h_{T_j}` satisfies the chapter's standing
  convention (Stacks 07SD), that the limits of its affine charts lie in the site
  (`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_affineYoneda`);
* the convention passes along a cartesian morphism of inverse systems
  (`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_cartesian`), and so to the system of
  base changes `X ×_Y T_j` of an algebraic space `X` over `Y`.

## Implementation notes

The convention is `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, the predicate the descent
library for Situation 084W is stated with: it quantifies over every stage, every affine point and
every lift of the diagram of base changes through the Yoneda embedding of the big affine site, a
chart system being exactly such a lift. On a cofiltered system it is read on chart systems by
`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_iff`.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Chart systems of an affine system, read in the site -/

section AffineChart

variable {I : Type u} [Category.{u} I] {D : I ⥤ BigAffineFppf B S hS} {i₀ : I}
  {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i₀))}
  (C : AffineChartSystem B S hS i₀ (D ⋙ affineYoneda B S hS) U₀ f₀)

namespace AffineChartSystem

/-- The projection of a chart of an affine system to its own stage, as a morphism of the site. -/
noncomputable def stageHom (k : Over i₀) :
    C.siteDiagram.obj k ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj k.left) :=
  yoneda.preimage (C.stageMap k)

/-- The projection of a chart of an affine system to `U₀`, as a morphism of the site. -/
noncomputable def baseHom (k : Over i₀) :
    C.siteDiagram.obj k ⟶ (BigAffineFppf.inclusion B S hS).obj U₀ :=
  yoneda.preimage (C.baseMap k)

/-- A chart of an affine system is the fibre product in the site of its stage with `U₀`. -/
theorem isPullback_stageHom_baseHom (k : Over i₀) :
    IsPullback (C.stageHom k) (C.baseHom k)
      ((BigAffineFppf.inclusion B S hS).map (D.map k.hom)) (yoneda.preimage f₀) := by
  have h : IsPullback (yoneda.map (C.stageHom k)) (yoneda.map (C.baseHom k))
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map k.hom)))
      (yoneda.map (yoneda.preimage f₀)) := by
    simp only [stageHom, baseHom, Functor.map_preimage]
    exact C.isPullback k
  exact h.of_map_of_faithful yoneda

/-- The projections of the charts of an affine system to their stages are natural. -/
theorem map_comp_stageHom {k k' : Over i₀} (m : k ⟶ k') :
    C.siteDiagram.map m ≫ C.stageHom k' =
      C.stageHom k ≫ (BigAffineFppf.inclusion B S hS).map (D.map m.left) := by
  apply yoneda.map_injective
  simp only [Functor.map_comp, stageHom, Functor.map_preimage]
  exact (C.stageMap_comp_map m).symm

/-- The projections of the charts of an affine system to `U₀` are compatible with the
transition morphisms. -/
theorem map_comp_baseHom {k k' : Over i₀} (m : k ⟶ k') :
    C.siteDiagram.map m ≫ C.baseHom k' = C.baseHom k := by
  apply yoneda.map_injective
  simp only [Functor.map_comp, baseHom, Functor.map_preimage]
  exact C.map_baseMap m

/-- The diagram of schemes underlying a chart system of an affine system is the diagram of base
changes of the stages along the point `U₀ ⟶ T_{i₀}`. -/
noncomputable def schemeDiagramIso :
    C.schemeDiagram ≅ (Over.post (X := i₀) (D ⋙ BigAffineFppf.toScheme B S hS) ⋙
      Over.pullback ((BigFppfOver.toScheme B S hS).map (yoneda.preimage f₀))) ⋙
        Over.forget _ := by
  let H := BigFppfOver.toScheme B S hS
  let incl := BigAffineFppf.inclusion B S hS
  let u₀ : incl.obj U₀ ⟶ incl.obj (D.obj i₀) := yoneda.preimage f₀
  let P : Over i₀ ⥤ Scheme.{u} :=
    (Over.post (X := i₀) (D ⋙ BigAffineFppf.toScheme B S hS) ⋙ Over.pullback (H.map u₀)) ⋙
      Over.forget _
  let Pfst : ∀ k : Over i₀, P.obj k ⟶ (D ⋙ BigAffineFppf.toScheme B S hS).obj k.left :=
    fun k => pullback.fst ((Over.post (X := i₀) (D ⋙ BigAffineFppf.toScheme B S hS)).obj k).hom
      (H.map u₀)
  let Psnd : ∀ k : Over i₀, P.obj k ⟶ H.obj (incl.obj U₀) :=
    fun k => pullback.snd ((Over.post (X := i₀) (D ⋙ BigAffineFppf.toScheme B S hS)).obj k).hom
      (H.map u₀)
  have PSq : ∀ k : Over i₀, IsPullback (Pfst k) (Psnd k)
      ((D ⋙ BigAffineFppf.toScheme B S hS).map k.hom) (H.map u₀) :=
    fun k => IsPullback.of_hasPullback _ _
  have hPf : ∀ {k k' : Over i₀} (m : k ⟶ k'),
      P.map m ≫ Pfst k' = Pfst k ≫ (D ⋙ BigAffineFppf.toScheme B S hS).map m.left := by
    intro k k' m
    dsimp [P, Pfst, Over.pullback, Over.post]
    simp only [Over.homMk_left, pullback.lift_fst]
  have hPs : ∀ {k k' : Over i₀} (m : k ⟶ k'), P.map m ≫ Psnd k' = Psnd k := by
    intro k k' m
    dsimp [P, Psnd, Over.pullback, Over.post]
    simp only [Over.homMk_left, pullback.lift_snd]
  have hsqH : ∀ k : Over i₀, IsPullback (H.map (C.stageHom k)) (H.map (C.baseHom k))
      ((D ⋙ BigAffineFppf.toScheme B S hS).map k.hom) (H.map u₀) :=
    fun k => (C.isPullback_stageHom_baseHom k).map H
  let ι : ∀ k : Over i₀, C.schemeDiagram.obj k ≅ P.obj k :=
    fun k => (hsqH k).isoIsPullback _ _ (PSq k)
  have he₁ : ∀ k : Over i₀, (ι k).hom ≫ Pfst k = H.map (C.stageHom k) :=
    fun k => IsPullback.isoIsPullback_hom_fst _ _ _ _
  have he₂ : ∀ k : Over i₀, (ι k).hom ≫ Psnd k = H.map (C.baseHom k) :=
    fun k => IsPullback.isoIsPullback_hom_snd _ _ _ _
  refine NatIso.ofComponents ι fun {k k'} m => (PSq k').hom_ext ?_ ?_
  · have e₁ : C.schemeDiagram.map m ≫ H.map (C.stageHom k') =
        H.map (C.stageHom k) ≫ (D ⋙ BigAffineFppf.toScheme B S hS).map m.left := by
      change H.map (C.siteDiagram.map m) ≫ H.map (C.stageHom k') =
        H.map (C.stageHom k) ≫ H.map (incl.map _)
      rw [← H.map_comp, ← H.map_comp, C.map_comp_stageHom m]
    rw [Category.assoc, Category.assoc, he₁ k', hPf m, ← Category.assoc (ι k).hom, he₁ k, e₁]
  · have e₂ : C.schemeDiagram.map m ≫ H.map (C.baseHom k') = H.map (C.baseHom k) := by
      change H.map (C.siteDiagram.map m) ≫ H.map (C.baseHom k') = H.map (C.baseHom k)
      rw [← H.map_comp, C.map_comp_baseHom m]
    rw [Category.assoc, Category.assoc, he₂ k', hPs m, he₂ k, e₂]

end AffineChartSystem

end AffineChart

/-! ### The representable system of an affine limit -/

section AffineSystem

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS)

/-- **The representable system of a cofiltered system of affine schemes whose limit in schemes
lies in the site satisfies the chapter's convention (Stacks 07SD).** The chart of a stage `T_k`
along an affine point `U₀ ⟶ T_{i₀}` is the fibre product `T_k ×_{T_{i₀}} U₀`, and the limit of
these fibre products in schemes is `T ×_{T_{i₀}} U₀`, the underlying scheme of a fibre product
in the site. -/
theorem siteContainsBaseChangeLimits_affineYoneda (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    SiteContainsBaseChangeLimits B S hS (D ⋙ affineYoneda B S hS) := by
  refine (siteContainsBaseChangeLimits_iff _).2 fun i₀ U₀ f₀ C => ?_
  classical
  have _ : IsConnected (Over i₀) := IsCofiltered.isConnected _
  let H := BigFppfOver.toScheme B S hS
  let incl := BigAffineFppf.inclusion B S hS
  let u₀ : incl.obj U₀ ⟶ incl.obj (D.obj i₀) := yoneda.preimage f₀
  have hP : IsLimit ((Over.forget _).mapCone ((Over.pullback (H.map u₀)).mapCone
      (((BigAffineFppf.toScheme B S hS).mapCone c).overPost i₀))) :=
    isLimitOfPreserves (Over.forget _) (isLimitOfPreserves (Over.pullback (H.map u₀))
      (hc.overPost i₀))
  refine exists_isLimit_contains_of_iso CategoryTheory.Equivalence.refl
    (C.schemeDiagramIso ≪≫ (Functor.leftUnitor _).symm) ⟨_, ⟨hP⟩, ?_⟩
  show (pullback (H.map (incl.map (c.π.app i₀))) (H.map u₀)).size < B.cutoff
  rw [← Scheme.size_congr (PreservesPullback.iso H (incl.map (c.π.app i₀)) u₀)]
  exact (pullback (incl.map (c.π.app i₀)) u₀).left.property

end AffineSystem

/-! ### Cartesian morphisms of inverse systems -/

section Cartesian

variable {I : Type u} [Category.{u} I] {Z D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (τ : Z ⟶ D)

/-- A chart system of `Z`, read through a cartesian morphism `τ : Z ⟶ D` of inverse systems, is a
chart system of `D` with the same diagram: the chart `Z_k ×_{Z_{i₀}} U₀` is `D_k ×_{D_{i₀}} U₀`
because `Z_k = D_k ×_{D_{i₀}} Z_{i₀}`. -/
noncomputable def AffineChartSystem.ofCartesian
    (hτ : ∀ {j k : I} (g : j ⟶ k), IsPullback (Z.map g) (τ.app j) (τ.app k) (D.map g))
    {i₀ : I} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z.obj i₀}
    (C : AffineChartSystem B S hS i₀ Z U₀ f₀) :
    AffineChartSystem B S hS i₀ D U₀ (f₀ ≫ τ.app i₀) where
  diagram := C.diagram
  iso :=
    let P : ∀ k : Over i₀, IsPullback (C.stageMap k ≫ τ.app k.left) (C.baseMap k)
        (D.map k.hom) (f₀ ≫ τ.app i₀) := fun k => (C.isPullback k).paste_horiz (hτ k.hom).flip
    let ι : ∀ k : Over i₀, (C.diagram ⋙ affineYoneda B S hS).obj k ≅
        (stageBaseChangeDiagram B S hS i₀ D U₀ (f₀ ≫ τ.app i₀)).obj k :=
      fun k => (P k).isoIsPullback _ _ (isPullback_stageBaseChange B S hS i₀ D U₀ _ k)
    have h₁ : ∀ k : Over i₀, (ι k).hom ≫
        stageBaseChangeFst B S hS i₀ D U₀ (f₀ ≫ τ.app i₀) k = C.stageMap k ≫ τ.app k.left :=
      fun k => IsPullback.isoIsPullback_hom_fst _ _ _ _
    have h₂ : ∀ k : Over i₀, (ι k).hom ≫
        stageBaseChangeSnd B S hS i₀ D U₀ (f₀ ≫ τ.app i₀) k = C.baseMap k :=
      fun k => IsPullback.isoIsPullback_hom_snd _ _ _ _
    NatIso.ofComponents ι (by
      intro k k' m
      change yoneda.map (C.siteDiagram.map m) ≫ (ι k').hom = (ι k).hom ≫ _
      apply (isPullback_stageBaseChange B S hS i₀ D U₀ (f₀ ≫ τ.app i₀) k').hom_ext
      · have e : yoneda.map (C.siteDiagram.map m) ≫ C.stageMap k' ≫ τ.app k'.left =
            C.stageMap k ≫ τ.app k.left ≫ D.map m.left := by
          rw [← Category.assoc, ← C.stageMap_comp_map m, Category.assoc, τ.naturality]
        rw [Category.assoc, Category.assoc,
          stageBaseChangeDiagram_map_comp_fst B S hS i₀ D U₀ (f₀ ≫ τ.app i₀) m,
          ← Category.assoc (ι k).hom, h₁ k, h₁ k', Category.assoc]
        exact e
      · rw [Category.assoc, Category.assoc,
          stageBaseChangeDiagram_map_comp_snd B S hS i₀ D U₀ (f₀ ≫ τ.app i₀) m, h₂ k, h₂ k']
        exact C.map_baseMap m)

/-- **The chapter's convention (Stacks 07SD) passes along cartesian morphisms of inverse
systems.** If `τ : Z ⟶ D` has cartesian naturality squares — for instance `Z` is the system of
base changes `D_j ×_Y X` along a morphism `X ⟶ Y` and compatible maps `D_j ⟶ Y` — then every
chart system of `Z` is a chart system of `D`, so the limits of the charts of `Z` lie in the site
whenever those of `D` do. -/
theorem siteContainsBaseChangeLimits_of_cartesian
    (hτ : ∀ {j k : I} (g : j ⟶ k), IsPullback (Z.map g) (τ.app j) (τ.app k) (D.map g))
    (hD : SiteContainsBaseChangeLimits B S hS D) : SiteContainsBaseChangeLimits B S hS Z :=
  fun i₀ U₀ f₀ W e =>
    let C : AffineChartSystem B S hS i₀ Z U₀ f₀ := ⟨W, e⟩
    hD i₀ U₀ (f₀ ≫ τ.app i₀) (C.ofCartesian τ hτ).diagram (C.ofCartesian τ hτ).iso

end Cartesian

/-! ### Limits of affine systems in the site and in presheaves -/

section AffineLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS)

/-- A cone of affine objects of the site whose underlying cone of schemes is limiting is
limiting in the big fppf site of `S`: the underlying-scheme functor reflects limits of connected
shape, the slice forgetting its structure morphism and the size-bounded subcategory being full. -/
noncomputable def isLimit_inclusion_mapCone_of_isLimit_toScheme (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    IsLimit ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  have _ : IsConnected I := IsCofiltered.isConnected I
  have h : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((BigAffineFppf.inclusion B S hS).mapCone c)) := hc
  exact isLimitOfReflects (BigFppfOver.toScheme B S hS) h

/-- A cone of affine objects of the site whose underlying cone of schemes is limiting represents
a limit of presheaves on the big fppf site of `S`. -/
noncomputable def isLimit_affineYoneda_mapCone_of_isLimit_toScheme (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    IsLimit ((affineYoneda B S hS).mapCone c) :=
  isLimitOfPreserves yoneda (isLimit_inclusion_mapCone_of_isLimit_toScheme D c hc)

end AffineLimit

/-! ### Limits along cartesian morphisms of inverse systems -/

section CartesianLimit

variable {C : Type*} [Category* C] {I : Type*} [Category* I] [IsCofiltered I]
  {Z D : I ⥤ C} (τ : Z ⟶ D)

/-- **A cone over a cartesian inverse system is limiting when it is cartesian over a limit.** Let
`τ : Z ⟶ D` be a morphism of cofiltered inverse systems all of whose naturality squares are
cartesian, `c'` a limit cone of `D`, and `cZ` a cone of `Z` with a morphism `p` of vertices
compatible with the projections, such that the square at one stage `j₀` is cartesian. Then `cZ`
is limiting: `Z_j = D_j ×_{D_{j₀}} Z_{j₀}` for `j ⟶ j₀`, so the limit of `Z` is the base change
of the limit of `D` to `Z_{j₀}`. -/
noncomputable def isLimitOfCartesian
    (hτ : ∀ {j k : I} (g : j ⟶ k), IsPullback (Z.map g) (τ.app j) (τ.app k) (D.map g))
    {c' : Cone D} (hc' : IsLimit c') (cZ : Cone Z) (p : cZ.pt ⟶ c'.pt)
    (hp : ∀ j, cZ.π.app j ≫ τ.app j = p ≫ c'.π.app j) (j₀ : I)
    (h₀ : IsPullback (cZ.π.app j₀) p (τ.app j₀) (c'.π.app j₀)) : IsLimit cZ := by
  classical
  let l : ∀ s : Cone Z, s.pt ⟶ c'.pt := fun s => hc'.lift ((Cone.postcompose τ).obj s)
  have hl : ∀ (s : Cone Z) (j : I), l s ≫ c'.π.app j = s.π.app j ≫ τ.app j :=
    fun s j => hc'.fac _ j
  let m : ∀ s : Cone Z, s.pt ⟶ cZ.pt := fun s => h₀.lift (s.π.app j₀) (l s) (hl s j₀).symm
  have hm₁ : ∀ s : Cone Z, m s ≫ cZ.π.app j₀ = s.π.app j₀ := fun s => h₀.lift_fst _ _ _
  have hm₂ : ∀ s : Cone Z, m s ≫ p = l s := fun s => h₀.lift_snd _ _ _
  have hfac : ∀ (s : Cone Z) (j : I), m s ≫ cZ.π.app j = s.π.app j := by
    intro s j
    let k := IsCofiltered.min j j₀
    let a : k ⟶ j := IsCofiltered.minToLeft j j₀
    let b : k ⟶ j₀ := IsCofiltered.minToRight j j₀
    have hk : m s ≫ cZ.π.app k = s.π.app k := by
      apply (hτ b).hom_ext
      · rw [Category.assoc, cZ.w, hm₁, s.w]
      · rw [Category.assoc, hp, ← Category.assoc, hm₂, hl]
    rw [← cZ.w a, ← Category.assoc, hk, s.w]
  exact
    { lift := m
      fac := hfac
      uniq := fun s m' hm' => by
        apply h₀.hom_ext
        · rw [hm' j₀, hm₁]
        · rw [hm₂]
          apply hc'.hom_ext
          intro j
          rw [Category.assoc, ← hp, ← Category.assoc, hm', hl] }

end CartesianLimit

/-! ### The system of base changes along a system of test schemes -/

section BaseChange

/-- The inclusion of algebraic spaces into presheaves preserves fibre products: the fibre
product of algebraic spaces is the presheaf fibre product. -/
private theorem preservesPullback_algebraicSpaces_ι {Y Z T : AlgebraicSpaces B S hS}
    (a : Y ⟶ T) (b : Z ⟶ T) :
    PreservesLimit (cospan a b) (ObjectProperty.ι (IsAlgebraicSpace B S hS)) :=
  have h := AlgebraicSpaces.isPullback_fiberProduct B S hS a b
  preservesLimit_of_preserves_limit_cone h.isLimit <|
    (isLimitMapConePullbackConeEquiv _ h.w).symm (IsPullback.of_hasPullback a.hom b.hom).isLimit

attribute [local instance] preservesPullback_algebraicSpaces_ι

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {I : Type u} [Category.{u} I]
  (E : I ⥤ SchemesOver Y)

/-- **The inverse system of base changes `X ×_Y T_j`**, as presheaves, along a system of test
schemes `T_j` over `Y`. -/
noncomputable def testBaseChangeSystem : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  E ⋙ baseChangeOver f ⋙ Over.forget X ⋙ ObjectProperty.ι _

/-- The projections `X ×_Y T_j ⟶ T_j` of the base changes to the test schemes, as a morphism of
inverse systems. -/
noncomputable def testBaseChangeSystemToTest :
    testBaseChangeSystem f E ⟶ E ⋙ CostructuredArrow.proj _ Y ⋙ yoneda where
  app j := (baseChangeInclusion f (E.obj j)).hom
  naturality _ _ g := congrArg (fun t => t.hom) (baseChangeMap_comp_inclusion f (E.map g))

/-- The projections of the base changes to the test schemes form a cartesian morphism of inverse
systems: `X ×_Y T_j = T_j ×_{T_k} (X ×_Y T_k)`. -/
theorem isPullback_testBaseChangeSystem {j k : I} (g : j ⟶ k) :
    IsPullback ((testBaseChangeSystem f E).map g) ((testBaseChangeSystemToTest f E).app j)
      ((testBaseChangeSystemToTest f E).app k)
      ((E ⋙ CostructuredArrow.proj _ Y ⋙ yoneda).map g) :=
  (isPullback_baseChangeMap f (E.map g)).map (ObjectProperty.ι _)

/-- **The base changes of a test scheme over `Y` lying over a limit of test schemes form a limit
of presheaves**: if `T = lim T_j` is a cofiltered limit of representable presheaves, then
`X ×_Y T = lim_j X ×_Y T_j`. -/
noncomputable def isLimit_testBaseChangeSystem [IsCofiltered I] (c : Cone E)
    (hc : IsLimit ((CostructuredArrow.proj _ Y ⋙ yoneda).mapCone c)) :
    IsLimit ((baseChangeOver f ⋙ Over.forget X ⋙ ObjectProperty.ι _).mapCone c) := by
  let j₀ : I := (IsCofiltered.nonempty (C := I)).some
  exact isLimitOfCartesian (testBaseChangeSystemToTest f E)
    (isPullback_testBaseChangeSystem f E) hc _
    (baseChangeInclusion f c.pt).hom
    (fun j => congrArg (fun t => t.hom) (baseChangeMap_comp_inclusion f (c.π.app j))) j₀
    ((isPullback_baseChangeMap f (c.π.app j₀)).map (ObjectProperty.ι _))

/-- **The system of base changes satisfies the chapter's convention (Stacks 07SD) when the system
of test schemes does.** -/
theorem siteContainsBaseChangeLimits_testBaseChangeSystem
    (h : SiteContainsBaseChangeLimits B S hS (E ⋙ CostructuredArrow.proj _ Y ⋙ yoneda)) :
    SiteContainsBaseChangeLimits B S hS (testBaseChangeSystem f E) :=
  siteContainsBaseChangeLimits_of_cartesian _ (isPullback_testBaseChangeSystem f E) h

end BaseChange

end AlgebraicGeometry.Space

end
