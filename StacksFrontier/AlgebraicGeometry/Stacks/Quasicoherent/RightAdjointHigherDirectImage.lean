module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleComparisonAcyclicity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf

/-!
# Higher direct images along a 1-morphism with a right adjoint

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`, presented strictly over the base, and suppose the functor `f` has a right adjoint
`G : 𝒴 ⥤ 𝒳`. This is the situation of a morphism of schemes `X ⟶ Y` read on the represented
categories, `G` being base change `V ↦ V ×_Y X`. Then:

* the direct image `f_*` of sheaves of modules of **Stacks 06WE** is the continuous pushforward
  along `G`, so that `(f_*ℱ)(y) = ℱ(G y)`;
* consequently (**Stacks 072W**) `Rⁱf_*ℱ` is the sheafification of `y ↦ Hⁱ(G y, ℱ)`, and it
  vanishes as soon as `Hⁱ(G y, ℱ)` does for the members `y` of a family of objects covering `𝒴`.

## Main definitions

* `AlgebraicGeometry.Stack.rightAdjointRingMap`: the map of structure sheaves `𝒪_𝒴 ⟶ G_*𝒪_𝒳`
  induced by the counit of `f ⊣ G`.
* `AlgebraicGeometry.Stack.moduleSheafPushforwardIsoOfRightAdjoint`: `f_*` is the continuous
  pushforward along `G`.

## Main results

* `AlgebraicGeometry.Stack.isZero_moduleSheafHigherDirectImage_of_rightAdjoint`: the vanishing
  criterion.

## Implementation notes

The inverse image of **Stacks 06WE** is the continuous pushforward along `f` for the identity of
the structure sheaf, and Mathlib's `SheafOfModules.pushforwardPushforwardAdj` makes the continuous
pushforward along `G` its right adjoint; the identification of the two right adjoints is
`CategoryTheory.Adjunction.rightAdjointUniq`. The structure functor of the source is taken to be
`f ⋙ q` on the nose, which is the presentation the higher direct images of **Stacks 076Z** use,
so the structure sheaf of the source is the restriction of that of the target by `rfl`.

No tag is recorded: this is bookkeeping toward the affine case of **Stacks 0765**.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Type (u + 1)} [Category.{u} 𝒳] [Category.{u} 𝒴]
  (q : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴)
  (hp : (f ⋙ q).IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  {G : 𝒴 ⥤ 𝒳} (adj : f ⊣ G)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

include hp hq adj in
/-- The right adjoint of a 1-morphism of categories fibred in groupoids is continuous for the
associated topologies, the 1-morphism itself being cocontinuous (Stacks 06NW). -/
theorem isContinuous_rightAdjoint_of_adjunction :
    G.IsContinuous (associatedTopology B S hS q τ) (associatedTopology B S hS (f ⋙ q) τ) :=
  have : (f ⋙ q).IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := isCocontinuous_of_isFiberedInGroupoids B S hS (f ⋙ q) q f τ hq rfl
  adj.isContinuous_of_isCocontinuous _ _

/-- **The map of structure sheaves along the right adjoint.** The map `𝒪_𝒴 ⟶ G_*𝒪_𝒳` whose
component at `y` is the restriction along the counit `f (G y) ⟶ y`. -/
noncomputable def rightAdjointRingMap :
    letI := isContinuous_rightAdjoint_of_adjunction B S hS q f hp hq adj τ
    ringStructureSheafCore B S hS q hq τ hτ ⟶
      (G.sheafPushforwardContinuous RingCat.{u} (associatedTopology B S hS q τ)
        (associatedTopology B S hS (f ⋙ q) τ)).obj
          (ringStructureSheafCore B S hS (f ⋙ q) hp τ hτ) :=
  ⟨Functor.whiskerRight (NatTrans.op adj.counit) (ringStructureSheafCore B S hS q hq τ hτ).obj⟩

/-- **The inverse image of Stacks 06WE is left adjoint to the continuous pushforward along the
right adjoint.** -/
noncomputable def modulePullbackAdjunctionOfRightAdjoint :
    letI := isContinuous_rightAdjoint_of_adjunction B S hS q f hp hq adj τ
    modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS (f ⋙ q) q hp hq f rfl τ hτ ⊣
      SheafOfModules.pushforward.{u + 1} (rightAdjointRingMap B S hS q f hp hq adj τ hτ) :=
  letI := isContinuous_rightAdjoint_of_adjunction B S hS q f hp hq adj τ
  have : (f ⋙ q).IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := isContinuous_of_isFiberedInGroupoids B S hS (f ⋙ q) q f τ hq rfl
  SheafOfModules.pushforwardPushforwardAdj adj
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS (f ⋙ q) q hp hq f rfl τ hτ)⟩
    (rightAdjointRingMap B S hS q f hp hq adj τ hτ)
    (by
      ext y : 2
      exact (Category.comp_id _).symm)
    (by
      ext x : 2
      let R := (ringStructureSheafCore B S hS q hq τ hτ).obj
      change 𝟙 _ ≫ R.map (adj.counit.app (f.obj x.unop)).op ≫
        R.map (f.map (adj.unit.app x.unop)).op = 𝟙 _
      rw [Category.id_comp, ← Functor.map_comp]
      exact (congrArg (fun k => R.map (Quiver.Hom.op k))
        (adj.left_triangle_components x.unop)).trans (R.map_id _))

/-- **The direct image of Stacks 06WE along a 1-morphism with a right adjoint `G` is the
continuous pushforward along `G`**: `(f_*ℱ)(y) = ℱ(G y)`. -/
noncomputable def moduleSheafPushforwardIsoOfRightAdjoint :
    letI := isContinuous_rightAdjoint_of_adjunction B S hS q f hp hq adj τ
    moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS (f ⋙ q) q hp hq f rfl τ hτ ≅
      SheafOfModules.pushforward.{u + 1} (rightAdjointRingMap B S hS q f hp hq adj τ hτ) :=
  (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS (f ⋙ q) q hp hq f rfl τ
    hτ).rightAdjointUniq
    (modulePullbackAdjunctionOfRightAdjoint B S hS q f hp hq adj τ hτ)

section Derived

variable [HasSheafify (associatedTopology B S hS (f ⋙ q) τ) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS (f ⋙ q) τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive

include adj in
/-- **The vanishing criterion for the higher direct images along a 1-morphism with a right
adjoint `G`.** If every object of `𝒴` is covered by members of a family `P` of objects, and the
cohomology `Hⁱ(G y, ℱ)` over `G y` vanishes for `y` in `P`, then `Rⁱf_*ℱ = 0`.

By `AlgebraicGeometry.Stack.moduleSheafPushforwardIsoOfRightAdjoint` the direct image is the
continuous pushforward along `G`, so by **Stacks 072W**
(`higherDirectImage_iso_sheafify_cohomologyPresheaf`) the sheaf `Rⁱf_*ℱ` is the sheafification of
the presheaf `y ↦ Hⁱ(G y, ℱ)`, whose sections die on the given coverings. -/
theorem isZero_moduleSheafHigherDirectImage_of_rightAdjoint (i : ℕ)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS (f ⋙ q) hp τ hτ))
    (P : 𝒴 → Prop)
    (hcov : ∀ y : 𝒴, ∃ (I : Type (u + 1)) (z : I → 𝒴) (π : ∀ j, z j ⟶ y),
      Sieve.ofArrows z π ∈ associatedTopology B S hS q τ y ∧ ∀ j, P (z j))
    (hvan : ∀ y : 𝒴, P y →
      letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS (f ⋙ q) hp τ hτ
      IsZero (((SheafOfModules.evaluation.{u + 1}
        (ringStructureSheafCore B S hS (f ⋙ q) hp τ hτ) (op (G.obj y))).rightDerived i).obj F)) :
    IsZero ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS (f ⋙ q) q hp hq f rfl
      τ hτ i).obj F) := by
  classical
  let := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS (f ⋙ q) hp τ hτ
  let := isContinuous_rightAdjoint_of_adjunction B S hS q f hp hq adj τ
  let O𝒳 := ringStructureSheafCore B S hS (f ⋙ q) hp τ hτ
  let O𝒴 := ringStructureSheafCore B S hS q hq τ hτ
  let ψ := rightAdjointRingMap B S hS q f hp hq adj τ hτ
  have : (SheafOfModules.pushforward.{u + 1} ψ).Additive :=
    (modulePullbackAdjunctionOfRightAdjoint B S hS q f hp hq adj τ hτ).right_adjoint_additive
  have : (cohFunctor G O𝒳 O𝒴 ψ).Additive := ⟨fun {_ _ _ _} => rfl⟩
  change IsZero (((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS (f ⋙ q) q hp hq f rfl
    τ hτ).rightDerived i).obj F)
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
    (moduleSheafPushforwardIsoOfRightAdjoint B S hS q f hp hq adj τ hτ) i).app F)
  obtain ⟨e⟩ := higherDirectImage_iso_sheafify_cohomologyPresheaf G O𝒳 O𝒴 ψ i F
  refine IsZero.of_iso ?_ e
  set Pr := cohPresheafModule G O𝒳 O𝒴 ψ i F
  have hPzero : ∀ y : 𝒴, P y → IsZero (Pr.obj (op y)) := by
    intro y hy
    obtain ⟨ey⟩ := cohPresheafModule_evaluation_iso G O𝒳 O𝒴 ψ i F y
    refine IsZero.of_iso ?_ ey
    rw [ModuleCat.isZero_iff_subsingleton]
    exact (ModuleCat.isZero_iff_subsingleton.1 (hvan y hy) :
      Subsingleton (cohomologyOverObject G O𝒳 i y F))
  suffices hz : IsZero ((presheafToSheaf (associatedTopology B S hS q τ) AddCommGrpCat.{u + 1}).obj
      Pr.presheaf) by
    have hz2 : IsZero ((SheafOfModules.toSheaf O𝒴).obj (moduleSheafification O𝒴 |>.obj Pr)) :=
      hz.of_iso ((PresheafOfModules.sheafificationCompToSheaf (𝟙 O𝒴.obj)).app Pr)
    rw [IsZero.iff_id_eq_zero]
    apply (SheafOfModules.toSheaf O𝒴).map_injective
    simpa using (IsZero.iff_id_eq_zero _).1 hz2
  refine Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero.{u + 1}
    (associatedTopology B S hS q τ) Pr.presheaf ?_
  intro U x
  obtain ⟨I, z, π, hc, hz⟩ := hcov U
  refine (associatedTopology B S hS q τ).superset_covering ?_ hc
  intro V g hg
  rw [Sieve.mem_ofArrows_iff] at hg
  obtain ⟨j, b, rfl⟩ := hg
  have hsub : Subsingleton (ToType (Pr.obj (op (z j)))) :=
    ModuleCat.isZero_iff_subsingleton.1 (hPzero (z j) (hz j))
  change Pr.presheaf.map (b ≫ π j).op x = Pr.presheaf.map (b ≫ π j).op 0
  rw [op_comp, Pr.presheaf.map_comp]
  have hmid : Pr.presheaf.map (π j).op x = Pr.presheaf.map (π j).op 0 := hsub.elim _ _
  simp only [ConcreteCategory.comp_apply, hmid]

end Derived

section SchemeStack

variable {X Y : BigFppfOver B S hS}

/-- **The functor of a 1-morphism of represented categories fibred in groupoids is
postcomposition with its underlying morphism of the site**, up to the canonical isomorphism
`AlgebraicGeometry.Stack.basedNatTransOfSchemeMapEq`, whose components lie over identities. -/
noncomputable def basedFunctorIsoOverMap
    (b : (schemeFibredCategory B S hS X).based ⥤ᵇ (schemeFibredCategory B S hS Y).based) :
    b.toFunctor ≅ Over.map (schemeMapOfFunctor B S hS b) :=
  let η := basedNatTransOfSchemeMapEq B S hS b
    (overMapBased B S hS (schemeMapOfFunctor B S hS b))
    (schemeMapOfFunctor_overMapBased B S hS _).symm
  NatIso.ofComponents
    (fun t => Over.isoMk
      (eqToIso ((b.w_obj t).trans
        ((overMapBased B S hS (schemeMapOfFunctor B S hS b)).w_obj t).symm))
      (Over.w (η.toNatTrans.app t)))
    (fun a => η.toNatTrans.naturality a)

/-- **A 1-morphism of represented algebraic stacks has a right adjoint**: base change along its
underlying morphism of the site. -/
noncomputable def schemeStackAdjunction
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) :
    CatFiberedInGroupoids.homFunctor f.hom ⊣ Over.pullback (schemeMapOfFunctor B S hS f.hom.hom) :=
  (Over.mapPullbackAdj (schemeMapOfFunctor B S hS f.hom.hom)).ofNatIsoLeft
    (basedFunctorIsoOverMap B S hS f.hom.hom).symm

/-- A fibre product of objects of the big fppf category over `S` lying over affine schemes lies
over an affine scheme. -/
theorem isAffine_toScheme_pullback {Z W V : BigFppfOver B S hS} (a : Z ⟶ V) (b : W ⟶ V)
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback a b)) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  exact @IsAffine.of_isIso _ _ (PreservesPullback.iso (BigFppfOver.toScheme B S hS) a b).hom
    inferInstance inferInstance

/-- **Stacks 0765, condition (4) of Stacks 076Z in positive degrees, from the affine acyclicity.**
Let `f` be a 1-morphism between the algebraic stacks represented by objects `X`, `Y` lying over
affine schemes, and `ℱ` an étale sheaf of modules on the source, with sections in `u + 1`, whose
higher cohomology over every object lying over an affine scheme vanishes in degree `i`. Then
`Rⁱf_*ℱ = 0`.

The functor of `f` has a right adjoint, base change along the underlying morphism of the site
(`AlgebraicGeometry.Stack.schemeStackAdjunction`); it carries an object over an affine scheme to
one over an affine scheme, `X` and `Y` being affine; and objects over affine schemes cover
(`AlgebraicGeometry.Stack.exists_affine_etale_ofArrows`). So
`AlgebraicGeometry.Stack.isZero_moduleSheafHigherDirectImage_of_rightAdjoint` applies. -/
theorem isZero_moduleSheafHigherDirectImage_schemeStack_of_affine
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) (i : ℕ)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hvan : ∀ x : (schemeStack.{u, t} B S hS X).val.val.obj,
      IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CatFiberedInGroupoids.homFunctor f.hom ⋙
          (schemeStack.{u, t} B S hS Y).val.val.p).obj x)) →
      letI := hasSheafify_associatedTopology_of_category_succ B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
      letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
      letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
        (etaleTopology_le_topology B)
      IsZero (((SheafOfModules.evaluation.{u + 1} (ringStructureSheafCore B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
        (etaleTopology_le_topology B)) (op x)).rightDerived i).obj F)) :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (schemeStack.{u, t} B S hS Y).val.val.p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (schemeStack.{u, t} B S hS Y).val.val.p
    IsZero ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
      (schemeStack.{u, t} B S hS Y).val.val.p
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
      (etaleTopology_le_topology B) i).obj F) := by
  let := hasSheafify_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
  let := hasSheafify_associatedTopology_of_category_succ B S hS
    (schemeStack.{u, t} B S hS Y).val.val.p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (schemeStack.{u, t} B S hS Y).val.val.p
  let c := schemeMapOfFunctor B S hS f.hom.hom
  refine isZero_moduleSheafHigherDirectImage_of_rightAdjoint B S hS
    (schemeStack.{u, t} B S hS Y).val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
    (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids
    (schemeStackAdjunction B S hS f) (etaleTopology B) (etaleTopology_le_topology B) i F
    (fun y => IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((schemeStack.{u, t} B S hS Y).val.val.p.obj y))) ?_ ?_
  · intro y
    obtain ⟨I, z, π, haff, -, -, hc⟩ := exists_affine_etale_ofArrows B S hS
      (schemeStack.{u, t} B S hS Y).val.val.p
      (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids y
    exact ⟨I, z, π, hc, haff⟩
  · intro y hy
    refine hvan _ ?_
    have hw : ((schemeStack.{u, t} B S hS Y).val.val.p.obj
          (f.hom.hom.obj ((Over.pullback c).obj y))) =
        ((Over.pullback c).obj y).left := f.hom.hom.w_obj _
    change IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((schemeStack.{u, t} B S hS Y).val.val.p.obj (f.hom.hom.obj ((Over.pullback c).obj y))))
    rw [hw]
    exact isAffine_toScheme_pullback B S hS _ _ hy hX hY

end SchemeStack

end AlgebraicGeometry.Stack

end
