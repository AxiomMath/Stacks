module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.Covering
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.DiscreteFunctionsSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.RingOfFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.IsSheafForOfLocalLifts

/-!
# The structure sheaf on the affine étale site

Let `X` be an fppf sheaf over `S` with a reduction `X_red`. Assume the correspondence of Stacks
0DEH between the affine étale formal charts `U ⟶ X` and the affine objects `W` of
`X_affine,étale`, read through reduction squares `W = U ×_X X_red`: every chart has a reduction,
every affine object is the reduction of a chart, and a morphism of reductions lifts uniquely to
a morphism of charts (`AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence`).
Then the rule of Section 0DEI,

`W ↦ 𝒪(U_W) = lim_{(T, x ∈ U_W(T))} Γ(T, 𝒪_T)`,

for `U_W` the chart with reduction `W`, is a sheaf of topological rings on `X_affine,étale`.
This is the proof of Stacks 0DEJ on `X_affine,étale`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.Reduction.IsReductionSquare`: a square exhibiting an affine
  object of `X_affine,étale` as the reduction `U ×_X X_red` of a chart.
* `AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence`: Stacks 0DEH, in terms of
  reduction squares.
* `AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence.chartFunctor`: the
  quasi-inverse `W ↦ U_W`.
* `AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence.affinePresheaf`: the rule of
  Section 0DEI, as a presheaf of topological rings on `X_affine,étale`.

## Main results

* `AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence.isSheaf_affinePresheaf`: it
  is a sheaf.

## Implementation notes

*The sheaf condition.* A presheaf of topological rings is a sheaf when, for every topological
ring `E`, the continuous ring maps from `E` form a sheaf of sets. Maps from `E` into the ring of
functions of `U_W` are natural families, over the affine points of `U_W`, of continuous ring
maps from `E` into the discrete rings `Γ(T, 𝒪_T)`
(`AlgebraicGeometry.FormalSpace.ringOfFunctionsHomEquiv`), and those form a sheaf on the big
affine fppf site (`AlgebraicGeometry.FormalSpace.isSheaf_discreteFunctions_comp_coyoneda`, which
is where the descent of Stacks 03OG and the finiteness of the coverings enter). The sheaf
condition then reduces to the two conditions of
`CategoryTheory.Presieve.isSheafFor_op_comp_yoneda_of_localLifts`: a point of `U_Y` lifts locally
to the charts of a covering — the base changes of the covering to an affine test object are an
étale covering of it (`AlgebraicGeometry.FormalSpace.mem_topology_of_jointly_surjective_points`)
— and two lifts are connected through the fibre product of two charts, which is a chart. This is
the argument of the source, with the limit over the stages `U_λ` replaced by the limit over all
affine points, which is the same limit
(`AlgebraicGeometry.FormalSpace.ThickeningPresentation.ringOfFunctionsIso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : FppfSheaf B S hS}

/-- The forgetful functor from the affine étale formal charts over `X` to fppf sheaves. -/
noncomputable abbrev AffineEtaleFormalCharts.forget (X : FppfSheaf B S hS) :
    AffineEtaleFormalCharts B S hS X ⥤ FppfSheaf B S hS :=
  ObjectProperty.ι _ ⋙ Over.forget X

namespace Reduction

variable (R : Reduction B S hS X)

/-- A *reduction square* for an affine étale formal chart `U ⟶ X` and an affine object `W` of
`X_affine,étale`: a morphism `a : W ⟶ U` exhibiting `W` as the fibre product `U ×_X X_red`. -/
abbrev IsReductionSquare (U : AffineEtaleFormalCharts B S hS X) (W : R.AffineEtale)
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left) : Prop :=
  IsPullback a (R.affineChartMap W) U.obj.hom R.inclusion

/-- **Stacks 0DEH, in terms of reduction squares.** The functor `U ↦ U ×_X X_red` from the
affine étale formal charts over `X` to `X_affine,étale` is an equivalence: every chart has a
reduction, every affine object of `X_affine,étale` is the reduction of a chart, and a morphism of
reductions lifts uniquely to a morphism of charts. -/
structure AffineEtaleCorrespondence : Prop where
  exists_square : ∀ U : AffineEtaleFormalCharts B S hS X, ∃ (W : R.AffineEtale)
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left), R.IsReductionSquare U W a
  exists_chart : ∀ W : R.AffineEtale, ∃ (U : AffineEtaleFormalCharts B S hS X)
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left), R.IsReductionSquare U W a
  existsUnique_hom : ∀ ⦃U V : AffineEtaleFormalCharts B S hS X⦄ ⦃W W' : R.AffineEtale⦄
    ⦃a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left⦄
    ⦃a' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W') ⟶
      V.obj.left⦄, R.IsReductionSquare U W a → R.IsReductionSquare V W' a' →
    ∀ h : W ⟶ W', ∃! g : U ⟶ V, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((Space.AffineEtale.toOver B S hS R.space.obj).map h) ≫ a' = a ≫ g.hom.left

namespace AffineEtaleCorrespondence

variable {R} (hC : R.AffineEtaleCorrespondence)

/-- The chart `U_W` whose reduction is `W`. -/
noncomputable def chart (W : R.AffineEtale) : AffineEtaleFormalCharts B S hS X :=
  (hC.exists_chart W).choose

/-- The reduction square of `U_W`. -/
noncomputable def chartMap (W : R.AffineEtale) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      (hC.chart W).obj.left :=
  (hC.exists_chart W).choose_spec.choose

/-- The square `hC.chartMap W` exhibits `W` as the reduction of the chart `hC.chart W`. -/
theorem isReductionSquare_chart (W : R.AffineEtale) :
    R.IsReductionSquare (hC.chart W) W (hC.chartMap W) :=
  (hC.exists_chart W).choose_spec.choose_spec

/-- The morphism of charts lifting a morphism of reductions. -/
noncomputable def chartHom {W W' : R.AffineEtale} (h : W ⟶ W') : hC.chart W ⟶ hC.chart W' :=
  (hC.existsUnique_hom (hC.isReductionSquare_chart W) (hC.isReductionSquare_chart W')
    h).exists.choose

/-- The morphism of charts `hC.chartHom h` is compatible with `h` through the reduction squares. -/
@[reassoc]
theorem chartHom_comm {W W' : R.AffineEtale} (h : W ⟶ W') :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map h) ≫ hC.chartMap W' =
      hC.chartMap W ≫ (hC.chartHom h).hom.left :=
  (hC.existsUnique_hom (hC.isReductionSquare_chart W) (hC.isReductionSquare_chart W')
    h).exists.choose_spec

/-- A morphism of charts compatible with `h` through the reduction squares is `hC.chartHom h`. -/
theorem eq_chartHom {W W' : R.AffineEtale} (h : W ⟶ W') (g : hC.chart W ⟶ hC.chart W')
    (hg : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map h) ≫ hC.chartMap W' =
      hC.chartMap W ≫ g.hom.left) : g = hC.chartHom h :=
  (hC.existsUnique_hom (hC.isReductionSquare_chart W) (hC.isReductionSquare_chart W') h).unique
    hg (hC.chartHom_comm h)

/-- **The quasi-inverse `W ↦ U_W` of Stacks 0DEH.** -/
noncomputable def chartFunctor : R.AffineEtale ⥤ AffineEtaleFormalCharts B S hS X where
  obj := hC.chart
  map := hC.chartHom
  map_id W := (hC.eq_chartHom (𝟙 W) (𝟙 _) (by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)).symm
  map_comp {W W' W''} f g := (hC.eq_chartHom (f ≫ g) (hC.chartHom f ≫ hC.chartHom g) (by
    let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
    let toOver := Space.AffineEtale.toOver B S hS R.space.obj
    calc sY.map (toOver.map (f ≫ g)) ≫ hC.chartMap W''
        = sY.map (toOver.map f) ≫ (sY.map (toOver.map g) ≫ hC.chartMap W'') := by
          rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc]
      _ = sY.map (toOver.map f) ≫ (hC.chartMap W' ≫ (hC.chartHom g).hom.left) := by
          rw [hC.chartHom_comm g]
      _ = (hC.chartMap W ≫ (hC.chartHom f).hom.left) ≫ (hC.chartHom g).hom.left := by
          rw [← Category.assoc, hC.chartHom_comm f]
      _ = hC.chartMap W ≫ (hC.chartHom f ≫ hC.chartHom g).hom.left := by
          rw [Category.assoc]
          rfl)).symm

/-- **The rule of Section 0DEI on `X_affine,étale`.** The presheaf of topological rings
`W ↦ 𝒪(U_W)`, the ring of functions of the chart with reduction `W`. -/
noncomputable def affinePresheaf : R.AffineEtaleᵒᵖ ⥤ TopCommRingCat.{u + 1} :=
  (hC.chartFunctor ⋙ AffineEtaleFormalCharts.forget X).op ⋙ ringOfFunctionsFunctor B S hS

/-- The affine points of the charts `U_W`. -/
noncomputable abbrev pointsFunctor : R.AffineEtale ⥤ ((BigAffineFppf B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  hC.chartFunctor ⋙ AffineEtaleFormalCharts.forget X ⋙ affinePoints B S hS

/-- The map of affine points induced by `h : W ⟶ W'` is that of the morphism of charts
`hC.chartHom h`. -/
theorem pointsFunctor_map_app {W W' : R.AffineEtale} (h : W ⟶ W') (T : BigAffineFppf B S hS)
    (x : (hC.pointsFunctor.obj W).obj (op T)) :
    (hC.pointsFunctor.map h).app (op T) x =
      (hC.chartHom h).hom.left.hom.app (op ((BigAffineFppf.inclusion B S hS).obj T)) x :=
  rfl

/-- Continuous ring maps from `E` into the rule of Section 0DEI are natural families of
continuous ring maps from `E` into the discrete rings of functions of the affine points. -/
noncomputable def affinePresheafCompCoyonedaIso (E : TopCommRingCat.{u + 1}) :
    hC.affinePresheaf ⋙ coyoneda.obj (op E) ≅
      hC.pointsFunctor.op ⋙ yoneda.obj (discreteFunctions B S hS ⋙ coyoneda.obj (op E)) :=
  NatIso.ofComponents (fun W => (ringOfFunctionsHomEquiv E _).toIso) (fun {W W'} h => by
    ext φ
    exact ringOfFunctionsHomEquiv_naturality E _ φ)

/-- A morphism `g` of `X_affine,étale` lies in a sieve if its image under the inclusion into
`X_étale` lies in the pushforward of the sieve, the inclusion being fully faithful. -/
theorem mem_of_mem_functorPushforward {Y Z : R.AffineEtale} {Sv : Sieve Y} (g : Z ⟶ Y)
    (hg : Sv.functorPushforward (Space.AffineEtale.inclusion B S hS R.space.obj)
      ((Space.AffineEtale.inclusion B S hS R.space.obj).map g)) : Sv g := by
  obtain ⟨Z', g', h', hg', heq⟩ := hg
  obtain ⟨h'', rfl⟩ := (Space.AffineEtale.inclusion B S hS R.space.obj).map_surjective h'
  rw [← Functor.map_comp] at heq
  rw [(Space.AffineEtale.inclusion B S hS R.space.obj).map_injective heq]
  exact Sv.downward_closed hg' h''

/-- **Local surjectivity.** For a covering sieve `Sv` of `Y` in `X_affine,étale`, every affine
point of `U_Y` lifts, locally on its affine test object, to the chart of a member of `Sv`. -/
theorem liftSieve_mem {Y : R.AffineEtale} {Sv : Sieve Y} (hSv : Sv ∈ R.affineEtaleTopology Y)
    (T : BigAffineFppf B S hS) (a : (hC.pointsFunctor.obj Y).obj (op T)) :
    Presieve.LocalLifts.liftSieve hC.pointsFunctor Sv a ∈ BigAffineFppf.topology B S hS T := by
  let G := Space.AffineEtale.inclusion B S hS R.space.obj
  have hdense : G.IsDenseSubsite (Space.AffineEtale.topology B S hS R.space.obj)
      (Space.SmallEtale.topology B S hS R.space.obj) :=
    (Space.AffineEtale.inclusion_isSpecialCocontinuous B S hS R.space.obj R.space.property).2
  have hpush : Sv.functorPushforward G ∈ Space.SmallEtale.topology B S hS R.space.obj (G.obj Y) :=
    (Functor.functorPushforward_mem_iff (G := G)
      (J := Space.AffineEtale.topology B S hS R.space.obj)
      (K := Space.SmallEtale.topology B S hS R.space.obj)).mpr hSv
  obtain ⟨P, hP, hPle⟩ := Space.AffineEtale.exists_covering_refining_pullback B S hS
    R.space.obj hpush (X := Y) (𝟙 _)
  obtain ⟨E, rfl, hE⟩ := (Space.AffineEtale.mem_precoverage_iff B S hS R.space.obj).mp hP
  have hES : ∀ k, Sv (E.f k) := fun k => mem_of_mem_functorPushforward (E.f k) (by
    simpa only [Category.comp_id] using hPle (E.f k) ⟨k⟩)
  have hf : ∀ y : (BigFppfOver.toScheme B S hS).obj (R.affineChartObj Y), ∃ k r,
      (BigFppfOver.toScheme B S hS).map ((Space.AffineEtale.toOver B S hS R.space.obj).map
        (E.f k)) r = y := ((Scheme.presieve₀_mem_precoverage_iff _).mp hE.1.2).1
  have hpoints := R.exists_pointsMapULift_eq_of_isPullback E.f hf (fun k => hC.chartHom (E.f k))
    (hC.isReductionSquare_chart Y) (fun k => hC.chartHom_comm (E.f k))
  refine (BigAffineFppf.topology B S hS).superset_covering ?_
    (mem_topology_of_jointly_surjective_points (fun k => hC.chartHom (E.f k)) hpoints T a)
  rintro T' t ⟨k, b, hb⟩
  exact ⟨E.X k, E.f k, hES k, b, hb⟩

/-- **Local injectivity.** Two lifts of an affine point of `U_Y` to the charts of two members of a
sieve are connected through the chart of their fibre product. -/
theorem exists_common_lift {Y Z₁ Z₂ : R.AffineEtale} (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y)
    (T : BigAffineFppf B S hS)
    (b₁ : (hC.chart Z₁).obj.left.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T)))
    (b₂ : (hC.chart Z₂).obj.left.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T)))
    (hb : (hC.chartHom g₁).hom.left.hom.app _ b₁ = (hC.chartHom g₂).hom.left.hom.app _ b₂) :
    ∃ (Z : R.AffineEtale) (h₁ : Z ⟶ Z₁) (h₂ : Z ⟶ Z₂), h₁ ≫ g₁ = h₂ ≫ g₂ ∧
      ∃ c : (hC.chart Z).obj.left.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T)),
        (hC.chartHom h₁).hom.left.hom.app _ c = b₁ ∧
        (hC.chartHom h₂).hom.left.hom.app _ c = b₂ := by
  let J := BigFppfOver.topology B S hS
  let sY := Sheaf.sheafifiedYoneda J
  let incl := BigAffineFppf.inclusion B S hS
  let toOver := Space.AffineEtale.toOver B S hS R.space.obj
  let u₁ := hC.chartHom g₁
  let u₂ := hC.chartHom g₂
  let V := AffineEtaleFormalCharts.pullbackChart u₁ u₂
  obtain ⟨W, aW, haW⟩ := hC.exists_square V
  obtain ⟨h₁, hh₁⟩ := R.exists_affineEtale_hom_of_isPullback haW (hC.isReductionSquare_chart Z₁)
    (AffineEtaleFormalCharts.pullbackFst u₁ u₂)
  obtain ⟨h₂, hh₂⟩ := R.exists_affineEtale_hom_of_isPullback haW (hC.isReductionSquare_chart Z₂)
    (AffineEtaleFormalCharts.pullbackSnd u₁ u₂)
  have hpb : AffineEtaleFormalCharts.pullbackFst u₁ u₂ ≫ u₁ =
      AffineEtaleFormalCharts.pullbackSnd u₁ u₂ ≫ u₂ := by
    exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext pullback.condition)
  -- composing a square-compatible morphism of charts with `hC.chartHom g`
  have hstep : ∀ {W' Z' : R.AffineEtale} (h : W ⟶ W') (ψ : V ⟶ hC.chart W') (g : W' ⟶ Z'),
      sY.map (toOver.map h) ≫ hC.chartMap W' = aW ≫ ψ.hom.left →
        sY.map (toOver.map (h ≫ g)) ≫ hC.chartMap Z' = aW ≫ (ψ ≫ hC.chartHom g).hom.left := by
    intro W' Z' h ψ g H
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      hC.chartHom_comm, ← Category.assoc, H, Category.assoc]
    rfl
  -- the two composites to `Y` agree, as they lie over the same morphism of charts
  have hcomm : h₁ ≫ g₁ = h₂ ≫ g₂ :=
    R.affineEtale_hom_ext_of_isPullback (a := aW) (hC.isReductionSquare_chart Y)
      (AffineEtaleFormalCharts.pullbackFst u₁ u₂ ≫ u₁) (hstep h₁ _ g₁ hh₁)
      (by rw [hpb]; exact hstep h₂ _ g₂ hh₂)
  -- the point of the fibre product
  have hb' : (Sheaf.sectionEquiv J).symm b₁ ≫ u₁.hom.left =
      (Sheaf.sectionEquiv J).symm b₂ ≫ u₂.hom.left := by
    apply (Sheaf.sectionEquiv J).injective
    simpa only [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply] using hb
  obtain ⟨p, hp₁, hp₂⟩ : ∃ p : sY.obj (incl.obj T) ⟶ V.obj.left,
      p ≫ (AffineEtaleFormalCharts.pullbackFst u₁ u₂).hom.left = (Sheaf.sectionEquiv J).symm b₁ ∧
        p ≫ (AffineEtaleFormalCharts.pullbackSnd u₁ u₂).hom.left =
          (Sheaf.sectionEquiv J).symm b₂ :=
    ⟨pullback.lift _ _ hb', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- the chart `U_W` is the fibre product
  obtain ⟨φ, hφ⟩ := (hC.existsUnique_hom haW (hC.isReductionSquare_chart W) (𝟙 W)).exists
  -- the point `p ≫ φ` of `U_W` maps to the given point of `U_{Z'}`
  have hpoint : ∀ {Z' : R.AffineEtale} (h : W ⟶ Z') (q : V ⟶ hC.chart Z')
      (b : (hC.chart Z').obj.left.obj.obj (op (incl.obj T))),
      sY.map (toOver.map h) ≫ hC.chartMap Z' = aW ≫ q.hom.left →
      p ≫ q.hom.left = (Sheaf.sectionEquiv J).symm b →
      (hC.chartHom h).hom.left.hom.app _ (Sheaf.sectionEquiv J (p ≫ φ.hom.left)) = b := by
    intro Z' h q b hq hpq
    have hφq : φ ≫ hC.chartHom h = q := by
      refine (hC.existsUnique_hom haW (hC.isReductionSquare_chart Z') h).unique ?_ hq
      simpa only [Category.id_comp] using hstep (𝟙 W) φ h hφ
    rw [← Sheaf.sectionEquiv_comp, Category.assoc,
      show φ.hom.left ≫ (hC.chartHom h).hom.left = q.hom.left from
        congrArg (fun k => k.hom.left) hφq,
      hpq, Equiv.apply_symm_apply]
  exact ⟨W, h₁, h₂, hcomm, Sheaf.sectionEquiv J (p ≫ φ.hom.left), hpoint h₁ _ b₁ hh₁ hp₁,
    hpoint h₂ _ b₂ hh₂ hp₂⟩

/-- **Stacks 0DEJ on `X_affine,étale`.** Under the correspondence of Stacks 0DEH, the rule of
Section 0DEI, `W ↦ 𝒪(U_W)`, is a sheaf of topological rings on `X_affine,étale`. -/
theorem isSheaf_affinePresheaf : Presheaf.IsSheaf R.affineEtaleTopology hC.affinePresheaf := by
  intro E
  refine Presieve.isSheaf_iso _ (hC.affinePresheafCompCoyonedaIso E).symm ?_
  intro Y Sv hSv
  refine Presieve.isSheafFor_op_comp_yoneda_of_localLifts (Φ := hC.pointsFunctor) (S := Sv)
    (isSheaf_discreteFunctions_comp_coyoneda E) (hC.liftSieve_mem hSv) ?_
  intro Z₁ Z₂ g₁ g₂ _ _ T b₁ b₂ hb
  obtain ⟨Z, h₁, h₂, hcomm, c, rfl, rfl⟩ := hC.exists_common_lift g₁ g₂ T b₁ b₂ hb
  exact ⟨⊤, (BigAffineFppf.topology B S hS).top_mem T, fun T' t _ =>
    ⟨Z, h₁, h₂, hcomm, _, NatTrans.naturality_apply (hC.pointsFunctor.map h₁) t.op c,
      NatTrans.naturality_apply (hC.pointsFunctor.map h₂) t.op c⟩⟩

end AffineEtaleCorrespondence

end Reduction

end AlgebraicGeometry.FormalSpace

end
