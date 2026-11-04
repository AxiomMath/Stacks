module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.ModuleAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek undoes inverse image on a chaotic site with an initial or final object

Let `C` be a category with the chaotic topology and let `π : Sh(C) ⟶ Sh(*)` be the point
morphism. If `C` has an initial or a final object, then `Lπ_! ∘ π^{-1}` is the identity, on
`D(Ab)` and on `D(B)` for a constant coefficient ring `B`.

The mathematical reason is that `π^{-1}` is the constant-diagram functor, and on a connected
category the constant functor is fully faithful with *both* a left and a right adjoint, namely
evaluation at an initial, respectively a final, object. Evaluation is exact, so one of the two
adjoints of `π^{-1}` is exact; in either case the counit of the resulting adjunction is an
isomorphism and descends to the derived categories.

## Main definitions

* `Stacks.ChaoticSite.trivialTopologySheafEquivalence`: for the chaotic topology, sheaves are
  presheaves.
* `Stacks.ChaoticSite.constantModuleSheafEquivalence`: modules over a constant sheaf of rings
  are diagrams of modules.

## Main results

* `Stacks.ChaoticSite.derivedConstCompColimitIso`: `Lπ_! ∘ π^{-1} = id` in the colimit
  presentation of lower shriek, with no existence hypothesis on the derived functor.
* `Stacks.ChaoticSite.abelianDerivedInverseImageCompLowerShriekIso`: the abelian-group case of
  `Lπ_! ∘ π^{-1} = id`.
* `Stacks.ChaoticSite.moduleDerivedInverseImageCompLowerShriekIso`: the case of sheaves of
  modules over a constant coefficient ring.

## Implementation notes

Both results are stated for an *arbitrary* model `L` of the total left derived functor of lower
shriek, presented by a comparison `α` exhibiting `L` as a left derived functor, and for an
arbitrary model `G` of the derived inverse image, presented by an isomorphism `e` with
degreewise inverse image on the homotopy category. Nothing is therefore assumed about the
existence of either derived functor, and the conclusion is a natural isomorphism of functors
rather than a family of objectwise isomorphisms. Both are consequences of the uniqueness of
left derived functors, so neither depends on the chosen models.

Two routes are needed, because only one of the two adjoints of the constant-diagram functor
exists in general. When `C` has an initial object, lower shriek itself is exact — it is
evaluation at that object up to isomorphism — and the comparison of `L` with the degreewise
derived functor of an exact functor is invertible. When `C` has only a final object, lower
shriek need not be exact; what is exact is then the *right* adjoint of `π^{-1}`, and the
identification is obtained by exhibiting `G ⋙ L` as a right Kan extension along `Qh`, using
that precomposition with the left adjoint of a localized adjunction preserves right Kan
extensions.

The adjunction on homotopy categories that Stacks 09T5 takes as input is
`CategoryTheory.Adjunction.mapHomotopyCategory`; it is used here rather than rebuilt.

The point of the site is `Discrete PUnit`, and `Stacks.ChaoticSite.pointConstEquiv` and
`Stacks.ChaoticSite.starWhiskerIso` identify presheaves on it with its coefficient category and
restriction along the point functor with the constant diagram; those two identifications are
reused here rather than rebuilt.

## References

* [Stacks Project, Tag 08Q7](https://stacks.math.columbia.edu/tag/08Q7)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChaoticSite

universe w v u uA vA m

attribute [local instance] HasDerivedCategory.standard

/-- For the chaotic topology every presheaf is a sheaf, so sheaves and presheaves agree. -/
@[sga "3 IV 4.4.2", sga "4 IV 6.8.6"]
def trivialTopologySheafEquivalence (C : Type u) [Category.{v} C]
    (A : Type uA) [Category.{vA} A] :
    Sheaf (GrothendieckTopology.trivial C) A ≌ (Cᵒᵖ ⥤ A) := by
  simpa only [GrothendieckTopology.trivial_eq_bot] using sheafBotEquivalence A

/-! ### Constant diagrams and the two adjoints of the constant functor -/

section Connected

variable (C : Type u) [Category.{v} C]

private lemma isConnected_of_hasInitial_or_hasTerminal (hC : HasInitial C ∨ HasTerminal C) :
    IsConnected C :=
  hC.elim (fun h => have := h; isConnected_of_hasInitial C)
    (fun h => have := h; isConnected_of_hasTerminal C)

/-- Evaluation of a diagram at a final object is left adjoint to the constant diagram. -/
@[sga "4 Vbis 1.2.11" "special case"]
private def evaluationConstAdjunction {J A : Type*} [Category* J] [Category* A] {obj : J}
    (hobj : IsTerminal obj) : (evaluation J A).obj obj ⊣ Functor.const J where
  unit := { app diagram := {
    app index := diagram.map (hobj.from index)
    naturality := by
      intro source target morphism
      dsimp
      rw [Category.comp_id, ← diagram.map_comp]
      exact congrArg diagram.map (hobj.hom_ext _ _) } }
  counit := { app _ := 𝟙 _ }
  left_triangle_components diagram := by
    dsimp
    rw [hobj.hom_ext (hobj.from obj) (𝟙 obj), diagram.map_id, Category.comp_id]
  right_triangle_components value := by ext index; simp

/-- Evaluation of a diagram at an initial object is right adjoint to the constant diagram. -/
@[sga "4 Vbis 1.2.11" "special case"]
private def constEvaluationAdjunction {J A : Type*} [Category* J] [Category* A] {obj : J}
    (hobj : IsInitial obj) : Functor.const J ⊣ (evaluation J A).obj obj where
  unit := { app _ := 𝟙 _ }
  counit := { app diagram := {
    app index := diagram.map (hobj.to index)
    naturality := by
      intro source target morphism
      dsimp
      rw [Category.id_comp, ← diagram.map_comp]
      exact congrArg diagram.map (hobj.hom_ext _ _) } }
  left_triangle_components value := by ext index; simp
  right_triangle_components diagram := by
    dsimp
    rw [hobj.hom_ext (hobj.to obj) (𝟙 obj), diagram.map_id, Category.id_comp]

end Connected

/-! ### Restriction along the point functor is the constant diagram -/

section PointPushforward

variable (C : Type u) [Category.{v} C] (A : Type uA) [Category.{vA} A]

/-- Restriction of diagrams along the point functor. -/
private abbrev starPrecomp : (((Discrete PUnit.{u + 1})ᵒᵖ) ⥤ A) ⥤ (Cᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft Cᵒᵖ ((Discrete PUnit.{u + 1})ᵒᵖ) A).obj (Functor.star C).op

/-- Diagrams on the one-object category are its coefficient category. -/
private abbrev pointEvaluationEquivalence : (((Discrete PUnit.{u + 1})ᵒᵖ) ⥤ A) ≌ A :=
  (pointConstEquiv A).symm

/-- Restriction along the point functor is evaluation at the point followed by the constant
diagram. This is `Stacks.ChaoticSite.starWhiskerIso`, read backwards. -/
private def starPrecompIso :
    starPrecomp C A ≅ (pointEvaluationEquivalence.{u} A).functor ⋙ Functor.const Cᵒᵖ :=
  (starWhiskerIso A C).symm

/-- For the chaotic topology, the forgetful functor from sheaves to presheaves is the underlying
functor of `trivialTopologySheafEquivalence`. -/
private def sheafToPresheafIso (C : Type u) [Category.{v} C] (A : Type uA) [Category.{vA} A] :
    sheafToPresheaf (GrothendieckTopology.trivial C) A ≅
      (trivialTopologySheafEquivalence C A).functor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simp [trivialTopologySheafEquivalence, sheafBotEquivalence])

/-- Restriction of sheaves along the point functor, read on underlying presheaves, is
restriction of diagrams. -/
private def pointPushforwardDiagramIso :
    ((Functor.star C).sheafPushforwardContinuous A
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))) ⋙
      (trivialTopologySheafEquivalence C A).functor ≅
    (trivialTopologySheafEquivalence (Discrete PUnit.{u + 1}) A).functor ⋙ starPrecomp C A := by
  exact (Functor.isoWhiskerLeft
      ((Functor.star C).sheafPushforwardContinuous A
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))) (sheafToPresheafIso C A)).symm ≪≫
    Functor.sheafPushforwardContinuousCompSheafToPresheafIso
      (Functor.star C) A (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) ≪≫
    Functor.isoWhiskerRight (sheafToPresheafIso (Discrete PUnit.{u + 1}) A) (starPrecomp C A)

/-- Restriction of sheaves along the point functor is the constant diagram at the value of the
sheaf on the point. -/
private def pointPushforwardConstIso :
    ((Functor.star C).sheafPushforwardContinuous A
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))) ⋙
      (trivialTopologySheafEquivalence C A).functor ≅
    ((trivialTopologySheafEquivalence (Discrete PUnit.{u + 1}) A).functor ⋙
      (pointEvaluationEquivalence.{u} A).functor) ⋙ Functor.const Cᵒᵖ :=
  pointPushforwardDiagramIso C A ≪≫
    Functor.isoWhiskerLeft
      (trivialTopologySheafEquivalence (Discrete PUnit.{u + 1}) A).functor
      (starPrecompIso C A) ≪≫ (Functor.associator _ _ _).symm

end PointPushforward

/-! ### Right Kan extensions along a localization and adjunctions -/

section KanExtension

variable {A B DA DB X : Type*} [Category* A] [Category* B]
  [Category* DA] [Category* DB] [Category* X]

/-- Precomposition with the left adjoint of a commuting pair of adjunctions transports the
universal property of a right Kan extension along `QA` to one along `QB`. -/
private def precompKanHomEquiv
    {H : B ⥤ A} {E : A ⥤ B} (adj : H ⊣ E)
    {H' : DB ⥤ DA} {E' : DA ⥤ DB} (adj' : H' ⊣ E')
    {QA : A ⥤ DA} {QB : B ⥤ DB} (comm : E ⋙ QB ≅ QA ⋙ E')
    {T : DA ⥤ X} {F : A ⥤ X} (α : QA ⋙ T ⟶ F)
    [T.IsRightKanExtension α] (K : DB ⥤ X) :
    (K ⟶ H' ⋙ T) ≃ (QB ⋙ K ⟶ H ⋙ F) :=
  ((adj'.whiskerLeft X).homEquiv K T).symm |>.trans
    (T.homEquivOfIsRightKanExtension α (E' ⋙ K)) |>.trans
    (Iso.homCongr ((Functor.associator E QB K).symm ≪≫
      Functor.isoWhiskerRight comm K ≪≫ Functor.associator QA E' K).symm
      (Iso.refl F)) |>.trans
    ((adj.whiskerLeft X).homEquiv (QB ⋙ K) F)

private lemma precompKanHomEquiv_naturality
    {H : B ⥤ A} {E : A ⥤ B} (adj : H ⊣ E)
    {H' : DB ⥤ DA} {E' : DA ⥤ DB} (adj' : H' ⊣ E')
    {QA : A ⥤ DA} {QB : B ⥤ DB} (comm : E ⋙ QB ≅ QA ⋙ E')
    {T : DA ⥤ X} {F : A ⥤ X} (α : QA ⋙ T ⟶ F)
    [T.IsRightKanExtension α] {K K' : DB ⥤ X}
    (η : K ⟶ K') (γ : K' ⟶ H' ⋙ T) :
    precompKanHomEquiv adj adj' comm α K (η ≫ γ) =
      Functor.whiskerLeft QB η ≫ precompKanHomEquiv adj adj' comm α K' γ := by
  dsimp [precompKanHomEquiv, Functor.homEquivOfIsRightKanExtension, Iso.homCongr]
  rw [adj'.whiskerLeft X |>.homEquiv_naturality_left_symm]
  simp only [Functor.whiskerLeft_comp, Category.assoc]
  rw [← adj.whiskerLeft X |>.homEquiv_naturality_left]
  congr 1
  ext obj
  dsimp
  simp only [Category.id_comp, Category.comp_id]
  rw [← η.naturality_assoc]

private theorem rightKanPrecompOfAdjunction
    {H : B ⥤ A} {E : A ⥤ B} (adj : H ⊣ E)
    {H' : DB ⥤ DA} {E' : DA ⥤ DB} (adj' : H' ⊣ E')
    {QA : A ⥤ DA} {QB : B ⥤ DB} (comm : E ⋙ QB ≅ QA ⋙ E')
    {T : DA ⥤ X} {F : A ⥤ X} (α : QA ⋙ T ⟶ F)
    [T.IsRightKanExtension α] :
    (H' ⋙ T).IsRightKanExtension
      (precompKanHomEquiv adj adj' comm α (H' ⋙ T) (𝟙 _)) := by
  let equiv := precompKanHomEquiv adj adj' comm α
  let δ := equiv (H' ⋙ T) (𝟙 _)
  refine ⟨⟨IsTerminal.ofUniqueHom (fun extension =>
    CostructuredArrow.homMk ((equiv extension.left).symm extension.hom) ?_) ?_⟩⟩
  · show Functor.whiskerLeft QB ((equiv extension.left).symm extension.hom) ≫ δ = _
    rw [← precompKanHomEquiv_naturality adj adj' comm α]
    simp [equiv]
  · intro extension morphism
    apply CostructuredArrow.hom_ext
    show morphism.left = (equiv extension.left).symm extension.hom
    apply (equiv extension.left).injective
    rw [Equiv.apply_symm_apply]
    have factor := CostructuredArrow.w morphism
    change Functor.whiskerLeft QB morphism.left ≫ δ = extension.hom at factor
    have naturality := precompKanHomEquiv_naturality adj adj' comm α morphism.left (𝟙 _)
    simp only [Category.comp_id] at naturality
    exact naturality.trans factor

end KanExtension

/-! ### The two derived identifications -/

section Derived

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- If the left adjoint `F` of a fully faithful `H` is exact, then any left derived functor of
`F` composed with any derived functor of `H` is the identity. -/
private def derivedCompositeOfExactLeftAdjoint
    {F : A ⥤ B} {H : B ⥤ A} [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [H.Full] [H.Faithful] (adj : F ⊣ H)
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]
    (G : DerivedCategory B ⥤ DerivedCategory A)
    (e : DerivedCategory.Qh ⋙ G ≅ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ := by
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ _
  let comparison := Functor.leftDerivedUnique F.mapDerivedCategory L α
    F.mapDerivedCategoryFactorsh.hom W
  let comm : DerivedCategory.Qh ⋙ (G ⋙ L) ≅ DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory B) :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e L ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (H.mapHomotopyCategory (.up ℤ))
      ((Functor.isoWhiskerLeft DerivedCategory.Qh comparison) ≪≫
        F.mapDerivedCategoryFactorsh) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit)
      DerivedCategory.Qh ≪≫
    Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (.up ℤ)) (DerivedCategory B)).preimageIso comm

/-- The same conclusion when it is the *right* adjoint `E` of a fully faithful `H` that is
exact: then `G ⋙ L` is a right Kan extension along `Qh`, as is the identity, so the two agree.
-/
def derivedCompositeOfExactRightAdjoint
    {F : A ⥤ B} {H : B ⥤ A} {E : A ⥤ B}
    [F.Additive] [H.Additive] [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [H.Full] [H.Faithful] (adj : F ⊣ H) (adjR : H ⊣ E)
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]
    (G : DerivedCategory B ⥤ DerivedCategory A)
    (e : DerivedCategory.Qh ⋙ G ≅ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ := by
  have : CatCommSq (H.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      DerivedCategory.Qh G := ⟨e.symm⟩
  have : CatCommSq (E.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      DerivedCategory.Qh E.mapDerivedCategory := ⟨E.mapDerivedCategoryFactorsh.symm⟩
  let derivedAdj := (adjR.mapHomotopyCategory (ComplexShape.up ℤ)).localization DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (.up ℤ)) DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ)) G E.mapDerivedCategory
  have : L.IsRightKanExtension α := Functor.IsLeftDerivedFunctor.isRightKanExtension
    L α (HomotopyCategory.quasiIso A (.up ℤ))
  let δ := precompKanHomEquiv (adjR.mapHomotopyCategory (ComplexShape.up ℤ)) derivedAdj
    E.mapDerivedCategoryFactorsh.symm α (G ⋙ L) (𝟙 _)
  have : (G ⋙ L).IsRightKanExtension δ := rightKanPrecompOfAdjunction
    (adjR.mapHomotopyCategory (ComplexShape.up ℤ)) derivedAdj E.mapDerivedCategoryFactorsh.symm α
  let counit : H.mapHomotopyCategory (.up ℤ) ⋙
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅ DerivedCategory.Qh :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit)
      DerivedCategory.Qh ≪≫
    Functor.leftUnitor _
  have : (𝟭 (DerivedCategory B)).IsLeftDerivedFunctor
      (Functor.rightUnitor DerivedCategory.Qh).hom
      (HomotopyCategory.quasiIso B (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ (Functor.rightUnitor _)
  have : (𝟭 (DerivedCategory B)).IsRightKanExtension
      (Functor.rightUnitor DerivedCategory.Qh).hom :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso B (.up ℤ))
  exact Functor.rightKanExtensionUniqueOfIso (G ⋙ L) δ counit (𝟭 _)
    (Functor.rightUnitor _).hom

variable {D : Type*} [Category* D] [Abelian D]

/-- Transport the constant-diagram presentation of `H` through the two equivalences. -/
private def transportedConstantIso {J : Type*} [Category* J]
    (source : A ≌ (J ⥤ D)) (point : B ≌ D)
    (H : B ⥤ A) (iso : H ⋙ source.functor ≅ point.functor ⋙ Functor.const J) :
    (point.functor ⋙ Functor.const J) ⋙ source.inverse ≅ H :=
  Functor.isoWhiskerRight iso.symm source.inverse ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft H source.unitIso.symm ≪≫ Functor.rightUnitor H

private def constantEvaluationLeftAdjunction {J : Type*} [Category* J]
    (source : A ≌ (J ⥤ D)) (point : B ≌ D)
    (H : B ⥤ A) (iso : H ⋙ source.functor ≅ point.functor ⋙ Functor.const J)
    {obj : J} (hobj : IsTerminal obj) :
    (source.functor ⋙ (evaluation J D).obj obj) ⋙ point.inverse ⊣ H :=
  ((source.toAdjunction.comp (evaluationConstAdjunction hobj)).comp
    point.symm.toAdjunction).ofNatIsoRight (transportedConstantIso source point H iso)

private def constantEvaluationRightAdjunction {J : Type*} [Category* J]
    (source : A ≌ (J ⥤ D)) (point : B ≌ D)
    (H : B ⥤ A) (iso : H ⋙ source.functor ≅ point.functor ⋙ Functor.const J)
    {obj : J} (hobj : IsInitial obj) :
    H ⊣ (source.functor ⋙ (evaluation J D).obj obj) ⋙ point.inverse :=
  ((point.toAdjunction.comp (constEvaluationAdjunction hobj)).comp
    source.symm.toAdjunction).ofNatIsoLeft (transportedConstantIso source point H iso)

/-- **The abstract form of Stacks 08Q7.** Let `A` be equivalent to the diagrams on `Cᵒᵖ` with
values in `D` and let `B` be equivalent to `D`, in such a way that a right adjoint `H` becomes
the constant diagram. If `C` has an initial or a final object, then any left derived functor `L`
of the left adjoint `F`, composed after any derived functor `G` of `H`, is the identity. -/
private def derivedCompositeOfConstant {C : Type*} [Category* C]
    (source : A ≌ (Cᵒᵖ ⥤ D)) (point : B ≌ D)
    (F : A ⥤ B) (H : B ⥤ A) [F.Additive] [H.Additive]
    (adj : F ⊣ H) (iso : H ⋙ source.functor ≅ point.functor ⋙ Functor.const Cᵒᵖ)
    (hC : HasInitial C ∨ HasTerminal C)
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]
    (G : DerivedCategory B ⥤ DerivedCategory A)
    (e : DerivedCategory.Qh ⋙ G ≅ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ := by
  have : IsConnected C := isConnected_of_hasInitial_or_hasTerminal C hC
  let ff := (Functor.FullyFaithful.comp point.fullyFaithfulFunctor
    (Functor.FullyFaithful.ofFullyFaithful (Functor.const Cᵒᵖ : D ⥤ _))).ofIso iso.symm
  have : (H ⋙ source.functor).Full := ff.full
  have : (H ⋙ source.functor).Faithful := ff.faithful
  have : H.Full := Functor.Full.of_comp_faithful H source.functor
  have : H.Faithful := Functor.Faithful.of_comp H source.functor
  classical
  apply Classical.choice
  rcases hC with hinitial | hterminal
  · have := hinitial
    let eval := (source.functor ⋙ (evaluation Cᵒᵖ D).obj (op (⊥_ C))) ⋙ point.inverse
    let evalAdj := constantEvaluationLeftAdjunction source point H iso initialIsInitial.op
    let comparison : F ≅ eval := Adjunction.leftAdjointUniq adj evalAdj
    have : PreservesFiniteLimits eval := inferInstance
    have : PreservesFiniteColimits eval := inferInstance
    have : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso comparison.symm
    have : PreservesFiniteColimits F := preservesFiniteColimits_of_natIso comparison.symm
    exact ⟨derivedCompositeOfExactLeftAdjoint adj L α G e⟩
  · have := hterminal
    let eval := (source.functor ⋙ (evaluation Cᵒᵖ D).obj (op (⊤_ C))) ⋙ point.inverse
    have : PreservesFiniteLimits eval := inferInstance
    have : PreservesFiniteColimits eval := inferInstance
    have : eval.Additive := by
      have := preservesBinaryBiproducts_of_preservesBinaryProducts eval
      exact Functor.additive_of_preservesBinaryBiproducts eval
    exact ⟨derivedCompositeOfExactRightAdjoint adj
      (constantEvaluationRightAdjunction source point H iso terminalIsTerminal.op) L α G e⟩

end Derived

/-! ### Modules over a constant sheaf of rings -/

section ConstantModules

variable {C : Type u} [Category.{v} C] (R : RingCat.{w})
  (S : Sheaf (GrothendieckTopology.trivial C) RingCat.{w})
  (eqRing : S.obj = (Functor.const Cᵒᵖ).obj R)

/-- A module over a constant sheaf of rings, read as a diagram of modules. -/
private def constantModuleDiagram :
    SheafOfModules.{uA} S ⥤ (Cᵒᵖ ⥤ ModuleCat.{uA} R) := by
  rcases S with ⟨presheaf, sheafCondition⟩
  dsimp at eqRing
  subst presheaf
  exact {
    obj module := {
      obj := module.val.obj
      map := module.val.map
      map_id obj := by
        ext value
        exact congrArg (fun morphism => morphism value) (module.val.map_id obj)
      map_comp first second := by
        ext value
        exact module.val.map_comp_apply first second value }
    map morphism := {
      app := morphism.val.app
      naturality first second restriction := by
        ext value
        exact PresheafOfModules.naturality_apply morphism.val restriction value }
    map_id module := by ext obj value; rfl
    map_comp first second := by ext obj value; rfl }

/-- **Modules over a constant sheaf of rings on a chaotic site are diagrams of modules.** -/
def constantModuleSheafEquivalence :
    SheafOfModules.{uA} S ≌ (Cᵒᵖ ⥤ ModuleCat.{uA} R) := by
  rcases S with ⟨presheaf, sheafCondition⟩
  dsimp at eqRing
  subst presheaf
  let S : Sheaf (GrothendieckTopology.trivial C) RingCat.{w} :=
    ⟨(Functor.const Cᵒᵖ).obj R, sheafCondition⟩
  refine {
    functor := constantModuleDiagram R S rfl
    inverse := {
      obj diagram := {
        val := {
          obj := diagram.obj
          map := diagram.map
          map_id obj := by
            ext value
            exact congrArg (fun morphism => morphism value) (diagram.map_id obj)
          map_comp first second := by
            ext value
            exact congrArg (fun morphism => morphism value) (diagram.map_comp first second) }
        isSheaf := by
          simpa only [GrothendieckTopology.trivial_eq_bot] using Presheaf.isSheaf_bot _ }
      map morphism := { val := {
        app := morphism.app
        naturality restriction := by
          ext value
          exact congrArg (fun morphism => morphism value) (morphism.naturality restriction) } }
      map_id diagram := by ext obj value; rfl
      map_comp first second := by ext obj value; rfl }
    unitIso := NatIso.ofComponents (fun module =>
      (SheafOfModules.fullyFaithfulForget S).preimageIso
        (PresheafOfModules.isoMk (fun _ => Iso.refl _)
          (by intro first second restriction; ext value; rfl)))
      (by intro first second morphism; ext obj value; rfl)
    counitIso := NatIso.ofComponents (fun diagram =>
      NatIso.ofComponents (fun _ => Iso.refl _)
        (by intro first second restriction; ext value; rfl))
      (by intro first second morphism; ext obj value; rfl)
    functor_unitIso_comp := ?_ }
  intro module
  ext obj value
  rfl

/-- **The diagram of modules attached to a module over a constant sheaf of rings is any diagram
with the same sections and the same restriction maps.** The equivalence is assembled from
`Stacks.ChaoticSite.constantModuleDiagram`, which is built by destructing the sheaf of rings and
is therefore reducible only where it is defined; this makes the sections of the diagram available
to its consumers, who otherwise cannot see that they are those of the module. -/
def constantModuleSheafEquivalenceFunctorObjIso
    (hS : Presheaf.IsSheaf (GrothendieckTopology.trivial C) ((Functor.const Cᵒᵖ).obj R))
    (M : SheafOfModules.{uA}
      (⟨(Functor.const Cᵒᵖ).obj R, hS⟩ : Sheaf (GrothendieckTopology.trivial C) RingCat.{w}))
    (D : Cᵒᵖ ⥤ ModuleCat.{uA} R) (e : ∀ V, M.val.obj V ≅ D.obj V)
    (he : ∀ {V W : Cᵒᵖ} (g : V ⟶ W) (x : M.val.obj V),
      (e W).hom (M.val.map g x) = D.map g ((e V).hom x)) :
    (constantModuleSheafEquivalence R ⟨(Functor.const Cᵒᵖ).obj R, hS⟩ rfl).functor.obj M ≅ D :=
  NatIso.ofComponents e (by intro V W g; ext x; exact he g x)

end ConstantModules

/-! ### Stacks 08Q7 -/

section Statement

variable (s : RingedPointSituation.{w, v, u})

/-- The constant sheaf of rings on the chaotic site of a ringed-point situation: the inverse
image of the coefficient ring along the point functor. -/
abbrev pointSituationConstantRing :
    Sheaf (GrothendieckTopology.trivial s.C) RingCat.{max w u v} :=
  pointInverseImageRing s.C (pointRing s)

/-- Restriction of a module along the point functor, read on diagrams, is the constant diagram.
-/
private def modulePushforwardDiagramIso :
    SheafOfModules.pushforward.{uA} (𝟙 (pointSituationConstantRing s)) ⋙
        (constantModuleSheafEquivalence ((forget₂ CommRingCat RingCat).obj s.B)
          (pointSituationConstantRing s) rfl).functor ≅
      (constantModuleSheafEquivalence ((forget₂ CommRingCat RingCat).obj s.B)
        (pointRing s) rfl).functor ⋙ starPrecomp s.C (ModuleCat.{uA} s.B) := by
  refine NatIso.ofComponents (fun module =>
    NatIso.ofComponents (fun _ => ?_) ?_) ?_
  · exact Iso.refl _
  · intro first second restriction
    ext value
    rfl
  · intro first second morphism
    ext obj value
    rfl

private def modulePushforwardConstIso :
    SheafOfModules.pushforward.{uA} (𝟙 (pointSituationConstantRing s)) ⋙
        (constantModuleSheafEquivalence ((forget₂ CommRingCat RingCat).obj s.B)
          (pointSituationConstantRing s) rfl).functor ≅
      ((constantModuleSheafEquivalence ((forget₂ CommRingCat RingCat).obj s.B)
        (pointRing s) rfl).functor ⋙
          (pointEvaluationEquivalence.{u} (ModuleCat.{uA} s.B)).functor) ⋙
        Functor.const s.Cᵒᵖ :=
  modulePushforwardDiagramIso s ≪≫
    Functor.isoWhiskerLeft
      (constantModuleSheafEquivalence ((forget₂ CommRingCat RingCat).obj s.B)
        (pointRing s) rfl).functor (starPrecompIso s.C (ModuleCat.{uA} s.B)) ≪≫
    (Functor.associator _ _ _).symm

/-- **Stacks 08Q7, unconditionally.** In the colimit presentation of lower shriek on a chaotic
site — `π_! = colim_{Cᵒᵖ}` and `π^{-1} = const` — the identity `Lπ_! ∘ π^{-1} = id` holds with no
hypothesis on the existence of the derived functor: the total left derived colimit of
`Stacks.CategoryHomology.totalDerivedColimit` exists for any coefficient category with enough
projectives and exact countable filtered colimits. -/
@[stacks 08Q7 "derived colimit presentation"]
def derivedConstCompColimitIso (C : Type u) [SmallCategory C]
    (Dc : Type uA) [Category.{vA} Dc] [Abelian Dc]
    [EnoughProjectives (Cᵒᵖ ⥤ Dc)] [HasColimitsOfShape ℕ Dc]
    [HasExactColimitsOfShape ℕ Dc] [HasColimitsOfShape Cᵒᵖ Dc]
    (hC : HasInitial C ∨ HasTerminal C) :
    (Functor.const Cᵒᵖ : Dc ⥤ (Cᵒᵖ ⥤ Dc)).mapDerivedCategory ⋙
      Stacks.CategoryHomology.totalDerivedColimit C Dc ≅ 𝟭 _ :=
  have := Stacks.CategoryHomology.colim_hasPointwiseLeftDerivedFunctor C Dc
  have := Stacks.CategoryHomology.totalDerivedColimit_isLeftDerivedFunctor C Dc
  derivedCompositeOfConstant (CategoryTheory.Equivalence.refl)
    (CategoryTheory.Equivalence.refl)
    (colim : (Cᵒᵖ ⥤ Dc) ⥤ Dc) (Functor.const Cᵒᵖ)
    (colimConstAdj : (colim : (Cᵒᵖ ⥤ Dc) ⥤ Dc) ⊣ Functor.const Cᵒᵖ)
    (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm) hC
    (Stacks.CategoryHomology.totalDerivedColimit C Dc)
    (Stacks.CategoryHomology.totalDerivedColimitCounit C Dc)
    (Functor.const Cᵒᵖ).mapDerivedCategory (Functor.const Cᵒᵖ).mapDerivedCategoryFactorsh

/-- **Stacks 08Q7, unconditionally, for a category that need not be small.** In the colimit
presentation of lower shriek on a chaotic site — `π_! = colim_{Cᵒᵖ}` and `π^{-1} = const` — the
identity `Lπ_! ∘ π^{-1} = id` holds with no hypothesis on the existence of the derived functor: the
total left derived colimit of `Stacks.CategoryHomology.totalDerivedColimit'` exists for any
coefficient category with enough projectives and exact countable filtered colimits.

No smallness is asked of the site either: the objects of `C` and its morphisms may live in
different universes, as they do at the site of [Stacks, Tag 08PR]. Everything the proof consumes
is size-general — `Stacks.CategoryHomology.totalDerivedColimit'` and its two companions
carry only instance hypotheses, and the abstract form `derivedCompositeOfConstant` is stated for
an arbitrary category. -/
@[stacks 08Q7 "derived colimit presentation"]
def derivedConstCompColimitIso' (C : Type u) [Category.{v} C]
    (Dc : Type uA) [Category.{vA} Dc] [Abelian Dc]
    [EnoughProjectives (Cᵒᵖ ⥤ Dc)] [HasColimitsOfShape ℕ Dc]
    [HasExactColimitsOfShape ℕ Dc] [HasColimitsOfShape Cᵒᵖ Dc]
    (hC : HasInitial C ∨ HasTerminal C) :
    (Functor.const Cᵒᵖ : Dc ⥤ (Cᵒᵖ ⥤ Dc)).mapDerivedCategory ⋙
      Stacks.CategoryHomology.totalDerivedColimit' C Dc ≅ 𝟭 _ :=
  have := Stacks.CategoryHomology.colim_hasPointwiseLeftDerivedFunctor' C Dc
  have := Stacks.CategoryHomology.totalDerivedColimit_isLeftDerivedFunctor' C Dc
  derivedCompositeOfConstant (CategoryTheory.Equivalence.refl)
    (CategoryTheory.Equivalence.refl)
    (colim : (Cᵒᵖ ⥤ Dc) ⥤ Dc) (Functor.const Cᵒᵖ)
    (colimConstAdj : (colim : (Cᵒᵖ ⥤ Dc) ⥤ Dc) ⊣ Functor.const Cᵒᵖ)
    (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm) hC
    (Stacks.CategoryHomology.totalDerivedColimit' C Dc)
    (Stacks.CategoryHomology.totalDerivedColimitCounit' C Dc)
    (Functor.const Cᵒᵖ).mapDerivedCategory (Functor.const Cᵒᵖ).mapDerivedCategoryFactorsh

/-- **Stacks 08Q7 for abelian sheaves.** On the chaotic site of a category with an initial or a
final object, inverse image from the point followed by derived lower shriek is the identity of
`D(Ab)`: for any left derived functor `L` of lower shriek, presented by a comparison `α`, and
any derived functor `G` of inverse image, presented by `e`, there is a natural isomorphism
`G ⋙ L ≅ 𝟭`. -/
@[stacks 08Q7 "abelian groups"]
def abelianDerivedInverseImageCompLowerShriekIso
    (C : Type u) [Category.{v} C]
    (hC : HasInitial C ∨ HasTerminal C)
    [HasSheafify (GrothendieckTopology.trivial C) AddCommGrpCat.{max w (u + 1) v}]
    [HasSheafify (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
      AddCommGrpCat.{max w (u + 1) v}]
    [((Functor.star C).sheafPushforwardContinuous AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).IsRightAdjoint]
    [((Functor.star C).sheafPullback AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).Additive]
    [((Functor.star C).sheafPushforwardContinuous AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).Additive]
    (L : DerivedCategory
      (Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{max w (u + 1) v}) ⥤
      DerivedCategory (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        AddCommGrpCat.{max w (u + 1) v}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((Functor.star C).sheafPullback AddCommGrpCat.{max w (u + 1) v}
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α
      (HomotopyCategory.quasiIso
        (Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{max w (u + 1) v})
        (ComplexShape.up ℤ))]
    (G : DerivedCategory (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        AddCommGrpCat.{max w (u + 1) v}) ⥤
      DerivedCategory (Sheaf (GrothendieckTopology.trivial C)
        AddCommGrpCat.{max w (u + 1) v}))
    (e : DerivedCategory.Qh ⋙ G ≅
      ((Functor.star C).sheafPushforwardContinuous AddCommGrpCat.{max w (u + 1) v}
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ :=
  derivedCompositeOfConstant
    (trivialTopologySheafEquivalence C AddCommGrpCat.{max w (u + 1) v})
    ((trivialTopologySheafEquivalence (Discrete PUnit.{u + 1})
      AddCommGrpCat.{max w (u + 1) v}).trans (pointEvaluationEquivalence.{u} _)) _ _
    ((Functor.star C).sheafAdjunctionContinuous AddCommGrpCat.{max w (u + 1) v}
      (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    (pointPushforwardConstIso C _) hC L α G e

/-- **Stacks 08Q7 for sheaves of modules.** The same identity for sheaves of modules over the
constant coefficient ring of a ringed-point situation whose category has an initial or a final
object. -/
@[stacks 08Q7 "modules over a ring"]
def moduleDerivedInverseImageCompLowerShriekIso
    (hC : HasInitial s.C ∨ HasTerminal s.C)
    [HasSheafify (GrothendieckTopology.trivial s.C) AddCommGrpCat.{max w u v}]
    [HasSheafify (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
      AddCommGrpCat.{max w u v}]
    [(GrothendieckTopology.trivial s.C).WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
    [(GrothendieckTopology.trivial (Discrete PUnit.{u + 1})).WEqualsLocallyBijective
      AddCommGrpCat.{max w u v}]
    [(SheafOfModules.pushforward (𝟙 (pointSituationConstantRing s))).IsRightAdjoint]
    [(SheafOfModules.pullback (𝟙 (pointSituationConstantRing s))).Additive]
    [(SheafOfModules.pushforward (𝟙 (pointSituationConstantRing s))).Additive]
    (L : DerivedCategory (SheafOfModules.{max w u v} (pointSituationConstantRing s)) ⥤
      DerivedCategory (SheafOfModules.{max w u v} (pointRing s)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      (SheafOfModules.pullback (𝟙 (pointSituationConstantRing s))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (G : DerivedCategory (SheafOfModules.{max w u v} (pointRing s)) ⥤
      DerivedCategory (SheafOfModules.{max w u v} (pointSituationConstantRing s)))
    (e : DerivedCategory.Qh ⋙ G ≅
      (SheafOfModules.pushforward (𝟙 (pointSituationConstantRing s))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ :=
  derivedCompositeOfConstant
    (constantModuleSheafEquivalence ((forget₂ CommRingCat RingCat).obj s.B)
      (pointSituationConstantRing s) rfl)
    ((constantModuleSheafEquivalence ((forget₂ CommRingCat RingCat).obj s.B)
      (pointRing s) rfl).trans (pointEvaluationEquivalence.{u} (ModuleCat.{max w u v} s.B)))
    _ _ (SheafOfModules.pullbackPushforwardAdjunction (𝟙 (pointSituationConstantRing s)))
    (modulePushforwardConstIso s) hC L α G e

end Statement

end Stacks.ChaoticSite

end
