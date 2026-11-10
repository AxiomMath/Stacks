module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupportCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterionBounded

/-!
# The base-change map of `f_!` on stalks

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'` locally of finite type, an
abelian sheaf `F` on the small étale site of `X`, and a geometric point `ȳ'` of `Y'` whose
spectrum lies in the site. This file carries out the stalk computation in the proof of
Stacks 0F55. The geometric fibre `X'_{ȳ'}` of `f'` and the geometric fibre `X_{g ∘ ȳ'}` of `f`
are identified by the comparison `e : X'_{ȳ'} ⟶ X_{g ∘ ȳ'}` of fibre products, an isomorphism
since the square is cartesian. The canonical maps of Stacks 0F76,
`(f_!F)_{g ∘ ȳ'} ⟶ H⁰_c(X_{g ∘ ȳ'}, F)` and `(f'_!(p⁻¹F))_{ȳ'} ⟶ H⁰_c(X'_{ȳ'}, p⁻¹F)`, then form
a commutative square with the stalk of the base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)` and the
bijection `H⁰_c(X_{g ∘ ȳ'}, F) ≅ H⁰_c(X'_{ȳ'}, p⁻¹F)` of pulling back along `e` (Stacks 0F74 for
the open immersion `e`), because all these maps pull local sections back along a commutative
diagram of morphisms of schemes. Hence the stalk of the base-change map is bijective as soon as
the two canonical maps are, which is what Stacks 0F76 asserts.

## Main definitions

* `AlgebraicGeometry.SmallEtale.geometricFibreComparison` — the isomorphism
  `e : X'_{ȳ'} ⟶ X_{g ∘ ȳ'}` of geometric fibres.
* `AlgebraicGeometry.SmallEtale.geometricFibreCompactSectionsEquiv` — the bijection
  `H⁰_c(X_{g ∘ ȳ'}, F) ≅ H⁰_c(X'_{ȳ'}, p⁻¹F)` of pulling back along `e`.

## Main results

* `AlgebraicGeometry.SmallEtale.pullbackSectionAlongHom_comp_arrow` — pulling sections back
  along two successive morphisms is pulling back along the composite, through the comparison of
  iterated inverse images.
* `AlgebraicGeometry.SmallEtale.properSupportBaseChange_stalk_germ` — the stalk of the
  base-change map on germs.
* `AlgebraicGeometry.SmallEtale.compactlySupportedSectionsPullbackIso` — Stacks 0F74 for an
  isomorphism: pulling back is a bijection of compactly supported sections.
* `AlgebraicGeometry.SmallEtale.fShriekStalkToCompactSections_properSupportBaseChange` — the
  commutative square of the proof of Stacks 0F55.
* `AlgebraicGeometry.SmallEtale.isIso_stalk_properSupportBaseChange` — the stalk of the
  base-change map is an isomorphism when the two canonical maps of Stacks 0F76 are bijective.
* `AlgebraicGeometry.SmallEtale.isIso_properSupportBaseChange_of_bijective` — hence the
  base-change map is an isomorphism when those maps are bijective at every geometric point
  whose spectrum lies in the site.

## References

* [Stacks Project, Tag 0F55](https://stacks.math.columbia.edu/tag/0F55)
* [Stacks Project, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)
* [Stacks Project, Tag 0F74](https://stacks.math.columbia.edu/tag/0F74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

section CompSections

variable (B : BigEtaleSite.{u}) {T₁ T₂ T₃ : B.Scheme} (q₁ : T₁ ⟶ T₂) (q₂ : T₂ ⟶ T₃) (q : T₁ ⟶ T₃)
  (hq : q₁ ≫ q₂ = q)
  (F : Sheaf (SmallEtale.topology B T₃.obj T₃.property) AddCommGrpCat.{max (u + 1) v})

/-- The composition law for pulling sections back along arbitrary arrows: pulling a section back
along `q₂` and then along `q₁` is, through the comparison of iterated inverse images, pulling it
back along a presentation `q` of `q₁ ≫ q₂`. -/
public theorem pullbackSectionAlongHom_comp_arrow (W : SmallEtale B T₃.obj T₃.property)
    (T : SmallEtale B T₂.obj T₂.property) (α : T ⟶ (smallEtaleBaseChange B q₂).obj W)
    (R : SmallEtale B T₁.obj T₁.property) (β : R ⟶ (smallEtaleBaseChange B q₁).obj T)
    (x : F.obj.obj (op W)) :
    ((smallEtaleSheafPullbackFactoredCompIso B T₁ T₂ T₃ q₁ q₂ q hq
          AddCommGrpCat.{max (u + 1) v}).hom.app F).hom.app (op R)
        (pullbackSectionAlongHom B q₁ AddCommGrpCat.{max (u + 1) v}
          ((abPullback.{u, v} B q₂).obj F) T R β
          (pullbackSectionAlongHom B q₂ AddCommGrpCat.{max (u + 1) v} F W T α x)) =
      pullbackSectionAlongHom B q AddCommGrpCat.{max (u + 1) v} F W R
        (β ≫ (smallEtaleBaseChange B q₁).map α ≫
          (smallEtaleBaseChange_factoredCompIso B T₁ T₂ T₃ q₁ q₂ q hq).hom.app W) x := by
  set cI := (smallEtaleSheafPullbackFactoredCompIso B T₁ T₂ T₃ q₁ q₂ q hq
    AddCommGrpCat.{max (u + 1) v}).hom.app F
  set G := (abPullback.{u, v} B q₂).obj F
  have h1 : pullbackSectionAlongHom B q₂ AddCommGrpCat.{max (u + 1) v} F W T α x =
      G.obj.map α.op (pullbackSectionAlongHom B q₂ AddCommGrpCat.{max (u + 1) v} F W
        ((smallEtaleBaseChange B q₂).obj W) (𝟙 _) x) := by
    rw [pullbackSectionAlongHom_restrict.{u, v}, Category.comp_id]
  have h3 := pullbackSectionAlongHom_restrict.{u, v} B q₁ G ((smallEtaleBaseChange B q₂).obj W)
    (𝟙 ((smallEtaleBaseChange B q₁).obj ((smallEtaleBaseChange B q₂).obj W)))
    (β ≫ (smallEtaleBaseChange B q₁).map α)
    (pullbackSectionAlongHom B q₂ AddCommGrpCat.{max (u + 1) v} F W
      ((smallEtaleBaseChange B q₂).obj W) (𝟙 _) x)
  rw [Category.comp_id] at h3
  have h4 := ConcreteCategory.congr_hom
    (cI.hom.naturality (β ≫ (smallEtaleBaseChange B q₁).map α).op)
    (pullbackSectionAlongHom B q₁ AddCommGrpCat.{max (u + 1) v} G
      ((smallEtaleBaseChange B q₂).obj W)
      ((smallEtaleBaseChange B q₁).obj ((smallEtaleBaseChange B q₂).obj W)) (𝟙 _)
      (pullbackSectionAlongHom B q₂ AddCommGrpCat.{max (u + 1) v} F W
        ((smallEtaleBaseChange B q₂).obj W) (𝟙 _) x))
  have h5 := ConcreteCategory.congr_hom (pullbackSectionAlongHom_comp B q₁ q₂ q hq
    AddCommGrpCat.{max (u + 1) v} F W) x
  simp only [ConcreteCategory.comp_apply] at h4 h5
  rw [h1, pullbackSectionAlongHom_map.{u, v}, ← h3]
  refine h4.trans ?_
  rw [h5, pullbackSectionAlongHom_restrict.{u, v}, Category.assoc]

end CompSections

section Fibres

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  (t : GeometricPoint Y'.obj) (ht : B.Contains t.source)

/-- The geometric point `g ∘ ȳ'` of `Y`, as a morphism of the big étale site, is `ȳ'` followed
by `g`. -/
public theorem geometricPointHom_map :
    geometricPointHom B (t.map (B.inclusion.map g)) ht = geometricPointHom B t ht ≫ g :=
  B.inclusion.map_injective (by simp)

include sq in
/-- The geometric fibre `X'_{ȳ'}` of `f'`, with the composite `X'_{ȳ'} ⟶ X' ⟶ X`, is a fibre
product of `f` and `g ∘ ȳ'`: the two cartesian squares paste. -/
public theorem isPullback_geometricFibre_comp :
    IsPullback (geometricFibreProj B f' t ht ≫ p) (geometricFibreStruct B f' t ht) f
      (geometricPointHom B (t.map (B.inclusion.map g)) ht) := by
  rw [geometricPointHom_map]
  exact ((IsPullback.of_hasPullback f' (geometricPointHom B t ht)).flip.paste_vert sq.flip).flip

/-- The comparison `e : X'_{ȳ'} ⟶ X_{g ∘ ȳ'}` of the geometric fibres of `f'` at `ȳ'` and of `f`
at `g ∘ ȳ'`, with components `X'_{ȳ'} ⟶ X' ⟶ X` and the structure morphism. -/
public def geometricFibreComparison :
    geometricFibreObj B f' t ht ⟶ geometricFibreObj B f (t.map (B.inclusion.map g)) ht :=
  (IsPullback.of_hasPullback f (geometricPointHom B (t.map (B.inclusion.map g)) ht)).lift
    (geometricFibreProj B f' t ht ≫ p) (geometricFibreStruct B f' t ht)
    (isPullback_geometricFibre_comp B p f' f g sq t ht).w

/-- The comparison of geometric fibres followed by the projection `X_{g ∘ ȳ'} ⟶ X` is the
composite `X'_{ȳ'} ⟶ X' ⟶ X`. -/
@[reassoc (attr := simp)]
public theorem geometricFibreComparison_proj :
    geometricFibreComparison B p f' f g sq t ht ≫
        geometricFibreProj B f (t.map (B.inclusion.map g)) ht =
      geometricFibreProj B f' t ht ≫ p :=
  IsPullback.lift_fst _ _ _ _

/-- The comparison of geometric fibres is compatible with the structure morphisms to the
geometric point. -/
@[reassoc (attr := simp)]
public theorem geometricFibreComparison_struct :
    geometricFibreComparison B p f' f g sq t ht ≫
        geometricFibreStruct B f (t.map (B.inclusion.map g)) ht =
      geometricFibreStruct B f' t ht :=
  IsPullback.lift_snd _ _ _ _

/-- The comparison of geometric fibres is an isomorphism, the square being cartesian. -/
public instance isIso_geometricFibreComparison :
    IsIso (geometricFibreComparison B p f' f g sq t ht) := by
  have h : geometricFibreComparison B p f' f g sq t ht =
      (IsPullback.isoIsPullback _ _ (isPullback_geometricFibre_comp B p f' f g sq t ht)
        (IsPullback.of_hasPullback f
          (geometricPointHom B (t.map (B.inclusion.map g)) ht))).hom :=
    (IsPullback.of_hasPullback f (geometricPointHom B (t.map (B.inclusion.map g)) ht)).hom_ext
      ((geometricFibreComparison_proj B p f' f g sq t ht).trans
        (IsPullback.isoIsPullback_hom_fst _ _ _ _).symm)
      ((geometricFibreComparison_struct B p f' f g sq t ht).trans
        (IsPullback.isoIsPullback_hom_snd _ _ _ _).symm)
  rw [h]
  infer_instance

/-- The neighbourhood of `ȳ'` given by base change along `g` of a neighbourhood of `g ∘ ȳ'`. -/
public abbrev baseChangeNeighborhood
    (N : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).Elements) :
    (geometricPointFiber B Y'.obj Y'.property t).Elements :=
  (geometricPointFiber B Y'.obj Y'.property t).elementsMk (baseChange B g N.1)
    (geometricPointFiberBaseChangeEquiv B g t N.1 N.2)

/-- The comparison of geometric fibres is compatible with the morphisms to the étale base
changes of a neighbourhood. -/
public theorem geometricFibreToNeighborhood_comp_fiberBaseChangeMap
    (N : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).Elements) :
    geometricFibreToNeighborhood B f' t ht (baseChangeNeighborhood B g t N) ≫
        fiberBaseChangeMap B p f' f g sq N.1 =
      geometricFibreComparison B p f' f g sq t ht ≫
        geometricFibreToNeighborhood B f (t.map (B.inclusion.map g)) ht N := by
  have hpt : neighborhoodPointHom B t ht (baseChangeNeighborhood B g t N) ≫
      fiberProjection B g N.1 = neighborhoodPointHom B (t.map (B.inclusion.map g)) ht N :=
    B.inclusion.map_injective ((B.inclusion.map_comp _ _).trans
      (geometricPointFiberBaseChangeEquiv_comp_fst B g t N.1 N.2))
  let A := geometricFibreToNeighborhood B f' t ht (baseChangeNeighborhood B g t N)
  let C := geometricFibreComparison B p f' f g sq t ht
  refine (isPullback_fiberProjection B f N.1).hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (A ≫ ·) (fiberBaseChangeMap_fst B p f' f g sq N.1)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ fiberProjection B g N.1)
        (geometricFibreToNeighborhood_fst B f' t ht (baseChangeNeighborhood B g t N))).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (geometricFibreStruct B f' t ht ≫ ·) hpt).trans <|
      (congrArg (· ≫ neighborhoodPointHom B (t.map (B.inclusion.map g)) ht N)
        (geometricFibreComparison_struct B p f' f g sq t ht).symm).trans <|
      (Category.assoc _ _ _).trans <| (congrArg (C ≫ ·)
        (geometricFibreToNeighborhood_fst B f (t.map (B.inclusion.map g)) ht N).symm).trans
      (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (A ≫ ·) (fiberBaseChangeMap_snd B p f' f g sq N.1)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ p)
        (geometricFibreToNeighborhood_snd B f' t ht (baseChangeNeighborhood B g t N))).trans <|
      (geometricFibreComparison_proj B p f' f g sq t ht).symm.trans <| (congrArg (C ≫ ·)
        (geometricFibreToNeighborhood_snd B f (t.map (B.inclusion.map g)) ht N).symm).trans
      (Category.assoc _ _ _).symm

/-- The two ways from the final object of the small étale site of `X'_{ȳ'}` to the base change of
`X_V` along `X'_{ȳ'} ⟶ X`: through the lift for `f'` and the comparison arrow of the square, and
through the comparison of fibres and the lift for `f`. -/
public theorem geometricFibreLift_comp_fiberBaseChangeArrow
    (N : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).Elements) :
    geometricFibreLift B f' t ht (baseChangeNeighborhood B g t N) ≫
        (smallEtaleBaseChange B (geometricFibreProj B f' t ht)).map
          (fiberBaseChangeArrow B p f' f g sq N.1) ≫
        (smallEtaleBaseChange_factoredCompIso B _ X' X (geometricFibreProj B f' t ht) p
          (geometricFibreProj B f' t ht ≫ p) rfl).hom.app (baseChange B f N.1) =
      (baseChangeFinalIso B (geometricFibreComparison B p f' f g sq t ht)).inv ≫
        (smallEtaleBaseChange B (geometricFibreComparison B p f' f g sq t ht)).map
          (geometricFibreLift B f (t.map (B.inclusion.map g)) ht N) ≫
        (smallEtaleBaseChange_factoredCompIso B _ _ X (geometricFibreComparison B p f' f g sq t ht)
          (geometricFibreProj B f (t.map (B.inclusion.map g)) ht)
          (geometricFibreProj B f' t ht ≫ p)
          (geometricFibreComparison_proj B p f' f g sq t ht)).hom.app (baseChange B f N.1) := by
  have hf1 : ((smallEtaleBaseChange_factoredCompIso B _ X' X (geometricFibreProj B f' t ht) p
        (geometricFibreProj B f' t ht ≫ p) rfl).hom.app (baseChange B f N.1)).hom.left ≫
        baseChangeObjProjection B (geometricFibreProj B f' t ht ≫ p) (baseChange B f N.1) =
      baseChangeObjProjection B (geometricFibreProj B f' t ht)
          ((smallEtaleBaseChange B p).obj (baseChange B f N.1)) ≫
        baseChangeObjProjection B p (baseChange B f N.1) :=
    smallEtaleBaseChange_factoredCompIso_hom_app_fst B _ X' X (geometricFibreProj B f' t ht) p
      (geometricFibreProj B f' t ht ≫ p) rfl _
  have hf2 : ((smallEtaleBaseChange_factoredCompIso B _ _ X
        (geometricFibreComparison B p f' f g sq t ht)
        (geometricFibreProj B f (t.map (B.inclusion.map g)) ht) (geometricFibreProj B f' t ht ≫ p)
        (geometricFibreComparison_proj B p f' f g sq t ht)).hom.app
        (baseChange B f N.1)).hom.left ≫
        baseChangeObjProjection B (geometricFibreProj B f' t ht ≫ p) (baseChange B f N.1) =
      baseChangeObjProjection B (geometricFibreComparison B p f' f g sq t ht)
          ((smallEtaleBaseChange B (geometricFibreProj B f (t.map (B.inclusion.map g)) ht)).obj
            (baseChange B f N.1)) ≫
        baseChangeObjProjection B (geometricFibreProj B f (t.map (B.inclusion.map g)) ht)
          (baseChange B f N.1) :=
    smallEtaleBaseChange_factoredCompIso_hom_app_fst B _ _ X
      (geometricFibreComparison B p f' f g sq t ht)
      (geometricFibreProj B f (t.map (B.inclusion.map g)) ht) (geometricFibreProj B f' t ht ≫ p) _ _
  have hfin : (baseChangeFinalIso B (geometricFibreComparison B p f' f g sq t ht)).inv.hom.left ≫
      baseChangeObjProjection B (geometricFibreComparison B p f' f g sq t ht)
        (SmallEtale.final B _ _) = geometricFibreComparison B p f' f g sq t ht :=
    B.inclusion.map_injective ((B.inclusion.map_comp _ _).trans
      (baseChangeFinalIso_inv_comp_fst B _))
  refine baseChangeObj_hom_ext B (geometricFibreProj B f' t ht ≫ p) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc, hf1, hf2,
    reassoc_of% baseChangeObjProjection_naturality, reassoc_of% geometricFibreLift_proj,
    reassoc_of% hfin]
  exact (congrArg (geometricFibreToNeighborhood B f' t ht (baseChangeNeighborhood B g t N) ≫ ·)
      (fiberBaseChangeArrow_proj B p f' f g sq N.1)).trans
    ((geometricFibreToNeighborhood_comp_fiberBaseChangeMap B p f' f g sq t ht N).trans
      (congrArg (geometricFibreComparison B p f' f g sq t ht ≫ ·)
        (geometricFibreLift_proj B f (t.map (B.inclusion.map g)) ht N).symm))

end Fibres

section Transport

variable (k : Type u) [Field k] (B : BigEtaleSite.{u}) {X Q₁ Q₂ : B.Scheme} (e : Q₁ ⟶ Q₂)
  [IsIso e] (a₂ : Q₂ ⟶ X) (a₁ : Q₁ ⟶ X) (ha : e ≫ a₂ = a₁)
  (b₂ : Q₂.obj ⟶ Spec (.of k)) [IsSeparated b₂] [LocallyOfFiniteType b₂]
  (b₁ : Q₁.obj ⟶ Spec (.of k)) [LocallyOfFiniteType b₁] (hb : B.inclusion.map e ≫ b₂ = b₁)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- Compactly supported sections along equal structure morphisms coincide. -/
public def compactlySupportedSectionsCongr (Q : B.Scheme) {m m' : Q.obj ⟶ Spec (.of k)}
    [LocallyOfFiniteType m] [LocallyOfFiniteType m'] (h : m = m')
    (G : Sheaf (SmallEtale.topology B Q.obj Q.property) AddCommGrpCat.{v}) :
    compactlySupportedSections k Q.obj m B Q.property G ≃+
      compactlySupportedSections k Q.obj m' B Q.property G :=
  AddEquiv.addSubgroupCongr (by subst h; rfl)

include hb in
/-- **Stacks 0F74** for an isomorphism `e : Q₁ ⟶ Q₂` over `X` and over `Spec k`: pulling back
along `e`, followed by the comparison of iterated inverse images, is a bijection
`H⁰_c(Q₂, F|_{Q₂}) ≅ H⁰_c(Q₁, F|_{Q₁})` of compactly supported sections. -/
public def compactlySupportedSectionsPullbackIso :
    compactlySupportedSections k Q₂.obj b₂ B Q₂.property ((abPullback.{u, v} B a₂).obj F) ≃+
      compactlySupportedSections k Q₁.obj b₁ B Q₁.property ((abPullback.{u, v} B a₁).obj F) :=
  let G := (abPullback.{u, v} B a₂).obj F
  let φ := compactlySupportedSections_openInclusion k B e b₂ G
  have hsurj : Function.Surjective φ.1 := fun t =>
    (exists_compactlySupportedSections_openInclusion_eq k B e b₂ G t).2 fun x _ =>
      Surjective.surj (f := B.inclusion.map e) x
  (AddEquiv.ofBijective φ.1 ⟨φ.2.1, hsurj⟩).symm.trans
    ((compactlySupportedSectionsMapIso k B Q₁ (B.inclusion.map e ≫ b₂)
      ((smallEtaleSheafPullbackFactoredCompIso B Q₁ Q₂ X e a₂ a₁ ha
        AddCommGrpCat.{max (u + 1) v}).app F)).trans
      (compactlySupportedSectionsCongr k B Q₁ hb ((abPullback.{u, v} B a₁).obj F)))

/-- The bijection of compactly supported sections along `e` is pulling a section back along `e`,
followed by the comparison of iterated inverse images. -/
public theorem compactlySupportedSectionsPullbackIso_apply
    (t : compactlySupportedSections k Q₂.obj b₂ B Q₂.property ((abPullback.{u, v} B a₂).obj F)) :
    (compactlySupportedSectionsPullbackIso k B e a₂ a₁ ha b₂ b₁ hb F t).1 =
      ((smallEtaleSheafPullbackFactoredCompIso B Q₁ Q₂ X e a₂ a₁ ha
        AddCommGrpCat.{max (u + 1) v}).hom.app F).hom.app
          (op (SmallEtale.final B Q₁.obj Q₁.property))
        (pullbackSectionAlongHom B e AddCommGrpCat.{max (u + 1) v}
          ((abPullback.{u, v} B a₂).obj F) (SmallEtale.final B Q₂.obj Q₂.property)
          (SmallEtale.final B Q₁.obj Q₁.property) (baseChangeFinalIso B e).inv t.1) := by
  let G := (abPullback.{u, v} B a₂).obj F
  let φ := compactlySupportedSections_openInclusion k B e b₂ G
  have hsurj : Function.Surjective φ.1 := fun t =>
    (exists_compactlySupportedSections_openInclusion_eq k B e b₂ G t).2 fun x _ =>
      Surjective.surj (f := B.inclusion.map e) x
  let Φ := AddEquiv.ofBijective φ.1 ⟨φ.2.1, hsurj⟩
  have hcomp : (baseChangeFinalIso B e).inv ≫
      (SmallEtale.finalIsTerminal B Q₁.obj Q₁.property).from
        ((smallEtaleBaseChange B e).obj (SmallEtale.final B Q₂.obj Q₂.property)) = 𝟙 _ :=
    (SmallEtale.finalIsTerminal B Q₁.obj Q₁.property).hom_ext _ _
  have h2 : ((abPullback.{u, v} B e).obj G).obj.map (baseChangeFinalIso B e).inv.op
      ((((smallEtaleBaseChange B e).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B Q₂.obj Q₂.property)
        (SmallEtale.topology B Q₁.obj Q₁.property)).unit.app G).hom.app
          (op (SmallEtale.final B Q₂.obj Q₂.property)) (φ.1 (Φ.symm t)).1) = (Φ.symm t).1 := by
    rw [← (φ.2.2 (Φ.symm t)).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      hcomp, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hφ : φ.1 (Φ.symm t) = t := Φ.apply_symm_apply t
  rw [hφ] at h2
  exact (congrArg (((smallEtaleSheafPullbackFactoredCompIso B Q₁ Q₂ X e a₂ a₁ ha
    AddCommGrpCat.{max (u + 1) v}).hom.app F).hom.app
      (op (SmallEtale.final B Q₁.obj Q₁.property))) h2).symm

end Transport

section Stalk

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f')]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (t : GeometricPoint Y'.obj)

/-- The stalk at `ȳ'` of the base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)`, read through the
identification of the stalk of `g⁻¹f_!F` at `ȳ'` with that of `f_!F` at `g ∘ ȳ'`, sends the germ
of a section of `f_!F` to the germ of its pullback to `X'_{V'}`. -/
public theorem properSupportBaseChange_stalk_germ
    (N : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).Elements)
    (s : ((properSupportFunctor B f).obj F).obj.obj (op N.1)) :
    (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{max (u + 1) v}).map
        (properSupportBaseChange.{u, v} B p f' f g sq F).hom
        ((etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{max (u + 1) v}
          ((properSupportFunctor B f).obj F)).inv
          (etaleGerm B Y.obj Y.property (t.map (B.inclusion.map g))
            ((properSupportFunctor B f).obj F).obj N.1 N.2 s)) =
      etaleGerm B Y'.obj Y'.property t
        ((properSupportFunctor B f').obj ((abPullback.{u, v} B p).obj F)).obj
        (baseChangeNeighborhood B g t N).1 (baseChangeNeighborhood B g t N).2
        ((properSupportBaseChangePushforward.{u, v} B p f' f g sq F).hom.app (op N.1) s) := by
  rw [etaleGerm_etaleStalkSmallEtalePullObjIso_inv B g t ((properSupportFunctor B f).obj F)
      (baseChange B g N.1) (geometricPointFiberBaseChangeEquiv B g t N.1 N.2) N.1 N.2 (𝟙 _)
      (geometricPointFiberBaseChangeEquiv_ha B g t N.1 N.2) s,
    etaleStalkPresheafFunctor_map_etaleGerm, pullbackSectionAlongHom_id]
  exact congrArg (etaleGerm B Y'.obj Y'.property t
    ((properSupportFunctor B f').obj ((abPullback.{u, v} B p).obj F)).obj
    (baseChange B g N.1) (geometricPointFiberBaseChangeEquiv B g t N.1 N.2))
    (ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun z => z.hom) (properSupportBaseChange_triangle.{u, v} B p f' f g sq F))
      (op N.1)) s)

variable (ht : B.Contains t.source)

/-- The structure morphism of a geometric fibre of a separated morphism is separated, being a
base change of it. -/
public instance isSeparated_geometricFibreStruct [IsSeparated (B.inclusion.map f)]
    (y : GeometricPoint Y.obj) (hy : B.Contains y.source) :
    IsSeparated (B.inclusion.map (geometricFibreStruct B f y hy)) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback f (geometricPointHom B y hy)).map B.inclusion) inferInstance

/-- The bijection `H⁰_c(X_{g ∘ ȳ'}, F) ≅ H⁰_c(X'_{ȳ'}, F)` of pulling back along the comparison of
geometric fibres, Stacks 0F74 for that isomorphism. -/
public def geometricFibreCompactSectionsEquiv [IsSeparated (B.inclusion.map f)] :
    geometricFibreCompactSections B f (t.map (B.inclusion.map g)) ht F ≃+
      compactlySupportedSections t.residueField (geometricFibreObj B f' t ht).obj
        (B.inclusion.map (geometricFibreStruct B f' t ht)) B (geometricFibreObj B f' t ht).property
        ((abPullback.{u, v} B (geometricFibreProj B f' t ht ≫ p)).obj F) :=
  compactlySupportedSectionsPullbackIso t.residueField B
    (geometricFibreComparison B p f' f g sq t ht)
    (geometricFibreProj B f (t.map (B.inclusion.map g)) ht) (geometricFibreProj B f' t ht ≫ p)
    (geometricFibreComparison_proj B p f' f g sq t ht)
    (B.inclusion.map (geometricFibreStruct B f (t.map (B.inclusion.map g)) ht))
    (B.inclusion.map (geometricFibreStruct B f' t ht))
    ((B.inclusion.map_comp _ _).symm.trans
      (congrArg B.inclusion.map (geometricFibreComparison_struct B p f' f g sq t ht))) F

/-- The underlying section of the image of `s` under `geometricFibreCompactSectionsEquiv` is the
pullback of `s` along the comparison of geometric fibres, followed by the comparison of iterated
inverse images. -/
public theorem geometricFibreCompactSectionsEquiv_apply [IsSeparated (B.inclusion.map f)]
    (s : geometricFibreCompactSections B f (t.map (B.inclusion.map g)) ht F) :
    (geometricFibreCompactSectionsEquiv.{u, v} B p f' f g sq F t ht s).1 =
      ((smallEtaleSheafPullbackFactoredCompIso B _ _ X
        (geometricFibreComparison B p f' f g sq t ht)
        (geometricFibreProj B f (t.map (B.inclusion.map g)) ht) (geometricFibreProj B f' t ht ≫ p)
        (geometricFibreComparison_proj B p f' f g sq t ht)
        AddCommGrpCat.{max (u + 1) v}).hom.app F).hom.app (op (SmallEtale.final B _ _))
        (pullbackSectionAlongHom B (geometricFibreComparison B p f' f g sq t ht)
          AddCommGrpCat.{max (u + 1) v} ((abPullback.{u, v} B
            (geometricFibreProj B f (t.map (B.inclusion.map g)) ht)).obj F)
          (SmallEtale.final B _ _) (SmallEtale.final B _ _)
          (baseChangeFinalIso B (geometricFibreComparison B p f' f g sq t ht)).inv s.1) :=
  compactlySupportedSectionsPullbackIso_apply.{u, v} t.residueField B _ _ _ _ _ _ _ F s

/-- The comparison `H⁰_c(X'_{ȳ'}, p⁻¹F) ≅ H⁰_c(X'_{ȳ'}, F)` of iterated inverse images on the
geometric fibre of `f'`. -/
public def geometricFibreCompSectionsEquiv :
    geometricFibreCompactSections B f' t ht ((abPullback.{u, v} B p).obj F) ≃+
      compactlySupportedSections t.residueField (geometricFibreObj B f' t ht).obj
        (B.inclusion.map (geometricFibreStruct B f' t ht)) B (geometricFibreObj B f' t ht).property
        ((abPullback.{u, v} B (geometricFibreProj B f' t ht ≫ p)).obj F) :=
  compactlySupportedSectionsMapIso t.residueField B (geometricFibreObj B f' t ht)
    (B.inclusion.map (geometricFibreStruct B f' t ht))
    ((smallEtaleSheafPullbackFactoredCompIso B _ X' X (geometricFibreProj B f' t ht) p
      (geometricFibreProj B f' t ht ≫ p) rfl AddCommGrpCat.{max (u + 1) v}).app F)

/-- The underlying section of the image of `s` under `geometricFibreCompSectionsEquiv` is the
comparison of iterated inverse images applied to `s`. -/
public theorem geometricFibreCompSectionsEquiv_apply
    (s : geometricFibreCompactSections B f' t ht ((abPullback.{u, v} B p).obj F)) :
    (geometricFibreCompSectionsEquiv.{u, v} B p f' F t ht s).1 =
      ((smallEtaleSheafPullbackFactoredCompIso B _ X' X (geometricFibreProj B f' t ht) p
        (geometricFibreProj B f' t ht ≫ p) rfl AddCommGrpCat.{max (u + 1) v}).hom.app F).hom.app
          (op (SmallEtale.final B _ _)) s.1 :=
  rfl

/-- **Stacks 0F55**, the commutative square of the proof: the canonical map of Stacks 0F76 for
`f'` at `ȳ'` after the stalk of the base-change map is the canonical map for `f` at `g ∘ ȳ'`,
through the identification of the stalk of an inverse image, the comparison of the geometric
fibres, and the comparison of iterated inverse images. -/
public theorem fShriekStalkToCompactSections_properSupportBaseChange
    [IsSeparated (B.inclusion.map f)]
    (z : ↑(etaleStalk B Y.obj Y.property (t.map (B.inclusion.map g))
      ((properSupportFunctor B f).obj F).obj)) :
    geometricFibreCompSectionsEquiv.{u, v} B p f' F t ht
        (fShriekStalkToCompactSections B f' t ht ((abPullback.{u, v} B p).obj F)
          ((etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{max (u + 1) v}).map
            (properSupportBaseChange.{u, v} B p f' f g sq F).hom
            ((etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{max (u + 1) v}
              ((properSupportFunctor B f).obj F)).inv z))) =
      geometricFibreCompactSectionsEquiv.{u, v} B p f' f g sq F t ht
        (fShriekStalkToCompactSections B f (t.map (B.inclusion.map g)) ht F z) := by
  obtain ⟨W, q, a, rfl⟩ := exists_etaleGerm_eq B Y.obj Y.property _ _ z
  apply Subtype.ext
  let N : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).Elements :=
    Functor.elementsMk _ W q
  let fc' := (smallEtaleSheafPullbackFactoredCompIso B _ X' X (geometricFibreProj B f' t ht) p
    (geometricFibreProj B f' t ht ≫ p) rfl AddCommGrpCat.{max (u + 1) v}).hom.app F
  let fc := (smallEtaleSheafPullbackFactoredCompIso B _ _ X
    (geometricFibreComparison B p f' f g sq t ht)
    (geometricFibreProj B f (t.map (B.inclusion.map g)) ht) (geometricFibreProj B f' t ht ≫ p)
    (geometricFibreComparison_proj B p f' f g sq t ht) AddCommGrpCat.{max (u + 1) v}).hom.app F
  have h2 := fShriekStalkToCompactSections_germ B f' t ht ((abPullback.{u, v} B p).obj F)
    (baseChangeNeighborhood B g t N)
    ((properSupportBaseChangePushforward.{u, v} B p f' f g sq F).hom.app (op N.1) a)
  have h3 := pullbackSectionAlongHom_comp_arrow.{u, v} B (geometricFibreProj B f' t ht) p
    (geometricFibreProj B f' t ht ≫ p) rfl F (baseChange B f W) _
    (fiberBaseChangeArrow B p f' f g sq W) _
    (geometricFibreLift B f' t ht (baseChangeNeighborhood B g t N)) a.1
  have h5 := pullbackSectionAlongHom_comp_arrow.{u, v} B
    (geometricFibreComparison B p f' f g sq t ht)
    (geometricFibreProj B f (t.map (B.inclusion.map g)) ht) (geometricFibreProj B f' t ht ≫ p)
    (geometricFibreComparison_proj B p f' f g sq t ht) F (baseChange B f W) _
    (geometricFibreLift B f (t.map (B.inclusion.map g)) ht N) _
    (baseChangeFinalIso B (geometricFibreComparison B p f' f g sq t ht)).inv a.1
  rw [geometricFibreCompSectionsEquiv_apply, geometricFibreCompactSectionsEquiv_apply]
  change fc'.hom.app _ (fShriekStalkToCompactSections B f' t ht ((abPullback.{u, v} B p).obj F)
    ((etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{max (u + 1) v}).map
      (properSupportBaseChange.{u, v} B p f' f g sq F).hom
      ((etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{max (u + 1) v}
        ((properSupportFunctor B f).obj F)).inv
        (etaleGerm B Y.obj Y.property (t.map (B.inclusion.map g))
          ((properSupportFunctor B f).obj F).obj N.1 N.2 a)))).1 = _
  rw [properSupportBaseChange_stalk_germ.{u, v} B p f' f g sq F t N a]
  refine (congrArg (fc'.hom.app _) h2).trans ?_
  refine h3.trans ?_
  rw [geometricFibreLift_comp_fiberBaseChangeArrow B p f' f g sq t ht N]
  refine h5.symm.trans ?_
  exact congrArg (fun m => fc.hom.app _ (pullbackSectionAlongHom B
    (geometricFibreComparison B p f' f g sq t ht) AddCommGrpCat.{max (u + 1) v} _
    (SmallEtale.final B _ _) (SmallEtale.final B _ _)
    (baseChangeFinalIso B (geometricFibreComparison B p f' f g sq t ht)).inv m))
    (fShriekStalkToCompactSections_germ B f (t.map (B.inclusion.map g)) ht F N a).symm

/-- **Stacks 0F55** on the stalk at a geometric point `ȳ'` whose spectrum lies in the site: the
stalk of the base-change map is an isomorphism as soon as the canonical maps of Stacks 0F76 for
`f` at `g ∘ ȳ'` and for `f'` at `ȳ'` are bijective. -/
public theorem isIso_stalk_properSupportBaseChange [IsSeparated (B.inclusion.map f)]
    (hc : Function.Bijective (fShriekStalkToCompactSections B f (t.map (B.inclusion.map g)) ht F))
    (hc' : Function.Bijective
      (fShriekStalkToCompactSections B f' t ht ((abPullback.{u, v} B p).obj F))) :
    IsIso ((etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{max (u + 1) v}).map
      (properSupportBaseChange.{u, v} B p f' f g sq F).hom) := by
  let κ := etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{max (u + 1) v}
    ((properSupportFunctor B f).obj F)
  let φ := (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{max (u + 1) v}).map
    (properSupportBaseChange.{u, v} B p f' f g sq F).hom
  let c := fShriekStalkToCompactSections B f (t.map (B.inclusion.map g)) ht F
  let c' := fShriekStalkToCompactSections B f' t ht ((abPullback.{u, v} B p).obj F)
  let E := geometricFibreCompactSectionsEquiv.{u, v} B p f' f g sq F t ht
  let E' := geometricFibreCompSectionsEquiv.{u, v} B p f' F t ht
  have hsq : ∀ z, E' (c' (φ (κ.inv z))) = E (c z) :=
    fShriekStalkToCompactSections_properSupportBaseChange.{u, v} B p f' f g sq F t ht
  have h1 : Function.Bijective fun z => φ (κ.inv z) := by
    refine ⟨fun z₁ z₂ h => hc.1 (E.injective ((hsq z₁).symm.trans
      ((congrArg (fun w => E' (c' w)) h).trans (hsq z₂)))), fun w => ?_⟩
    obtain ⟨z, hz⟩ := hc.2 (E.symm (E' (c' w)))
    exact ⟨z, hc'.1 (E'.injective ((hsq z).trans
      ((congrArg E hz).trans (AddEquiv.apply_symm_apply E _))))⟩
  have hκ : Function.Bijective κ.inv :=
    (ConcreteCategory.isIso_iff_bijective κ.inv).mp inferInstance
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr ((Function.Bijective.of_comp_iff φ hκ).mp h1)

end Stalk

section Global

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f')]
  [IsSeparated (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- **Stacks 0F55**, the reduction to Stacks 0F76: the base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)` is
an isomorphism as soon as, at every geometric point `ȳ'` of `Y'` whose spectrum lies in the
site, the canonical maps of Stacks 0F76 for `f` at `g ∘ ȳ'` and for `f'` at `ȳ'` are bijective;
the stalks at those points detect isomorphisms. -/
public theorem isIso_properSupportBaseChange_of_bijective
    (h : ∀ (t : GeometricPoint Y'.obj) (ht : B.Contains t.source),
      Function.Bijective
          (fShriekStalkToCompactSections B f (t.map (B.inclusion.map g)) ht F) ∧
        Function.Bijective
          (fShriekStalkToCompactSections B f' t ht ((abPullback.{u, v} B p).obj F))) :
    IsIso (properSupportBaseChange.{u, v} B p f' f g sq F) :=
  isIso_of_isIso_etaleStalkMap_bounded.{u, max (u + 1) v} B Y'.property _ fun t ht =>
    isIso_stalk_properSupportBaseChange.{u, v} B p f' f g sq F t ht (h t ht).1 (h t ht).2

end Global

end AlgebraicGeometry.SmallEtale

end
