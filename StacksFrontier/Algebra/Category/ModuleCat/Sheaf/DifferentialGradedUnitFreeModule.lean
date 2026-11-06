module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksCore.Tactic.StacksAttribute

/-!
# Free complexes with zero differential on presheaves of sets are good

Let `(C, O)` be a ringed site and let `P : ℤ → (Cᵒᵖ ⥤ Type)` be a family of presheaves of sets.
The complex `O[P]` with zero differential whose degree-`n` term is the sheafification of the free
`O`-module on `P n` is a right differential graded `(O, 0)`-module. **It is the free
differential graded `(O, 0)`-module on a sheaf of graded sets**, namely the sheafification `T` of
the presheaf `U ↦ ⨿ₙ P n (U)` graded by `n`: its morphisms into any `Q` are naturally the
families of morphisms from the sheaves of degree-`i` local sections of `T` to the closed
degree-`i` local sections of `Q`, and the coYoneda lemma identifies it with `(O, 0)[T]`. So by
Tag 0FSG it is good in the sense of Tag 0FSA.

This is the form in which the weight pieces of a free graded algebra are free: their generators
are words, which form a presheaf of graded sets and not a sheaf.

## Main definitions

* `SheafOfModules.freePieceOf F`: the sheafification of the free `O`-module on a presheaf of sets
  `F`, with `freeGen` its canonical local sections, `freePieceDesc` the morphism out of it
  prescribed on the canonical sections and `freePieceMap` its functoriality.
* `SheafOfModules.freeOnPresheaves P`: the complex `O[P]` with zero differential, as a right
  differential graded `(O, 0)`-module.
* `SheafOfModules.gradedSetOfPresheaves P`: the sheaf of graded sets `T`.

## Main results

* `SheafOfModules.freePieceOf_hom_ext`: a morphism out of `freePieceOf F` is determined by its
  values on the canonical sections.
* `SheafOfModules.degreeFiberSheafIsoOfPresheaves`: the sheaf of degree-`i` local sections of
  `T` is the sheafification of `P i`.
* `SheafOfModules.freeOnPresheavesIsoFreeDGModule`: `O[P] ≅ (O, 0)[T]`.
* `SheafOfModules.freeOnPresheaves_isGoodToposBaseChange`: **`O[P]` is good.**

## References

* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe t v u w v₁ u₁ v₂ u₂

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets DifferentialGradedModule unitDGAlgebra

section FreePiece

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

variable (Osharp) in
/-- The sheafification of the free `O`-module on a presheaf of sets. -/
noncomputable def freePieceOf (F : Cᵒᵖ ⥤ Type t) : SheafOfModules.{t} (toRingCat J Osharp) :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
    (PresheafOfModules.freeObj (R := (toRingCat J Osharp).obj) F)

variable (Osharp) in
/-- The canonical morphism from the free presheaf of modules to its sheafification. -/
noncomputable def freeToSheaf (F : Cᵒᵖ ⥤ Type t) :
    PresheafOfModules.freeObj (R := (toRingCat J Osharp).obj) F ⟶ (freePieceOf Osharp F).val :=
  PresheafOfModules.toSheafify (𝟙 (toRingCat J Osharp).obj)
    (CategoryTheory.toSheafify J
      (PresheafOfModules.freeObj (R := (toRingCat J Osharp).obj) F).presheaf)

/-- The canonical morphism from the free presheaf of modules to its sheafification is locally
surjective. -/
instance (F : Cᵒᵖ ⥤ Type t) :
    PresheafOfModules.IsLocallySurjective J (freeToSheaf Osharp F) :=
  inferInstanceAs (PresheafOfModules.IsLocallySurjective J
    (PresheafOfModules.toSheafify (𝟙 (toRingCat J Osharp).obj) _))

variable (Osharp) in
/-- The canonical local sections of `freePieceOf F`, as a morphism of presheaves of sets. -/
noncomputable def freeGenNat (F : Cᵒᵖ ⥤ Type t) :
    F ⟶ (freePieceOf Osharp F).val.presheaf ⋙ CategoryTheory.forget _ :=
  PresheafOfModules.freeAdjunctionUnit _ F ≫
    Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map (freeToSheaf Osharp F))
      (CategoryTheory.forget _)

variable (Osharp) in
/-- The canonical local section of `freePieceOf F` attached to a local section of `F`. -/
noncomputable def freeGen {F : Cᵒᵖ ⥤ Type t} {U : Cᵒᵖ} (p : F.obj U) :
    (freePieceOf Osharp F).val.obj U :=
  (freeGenNat Osharp F).app U p

/-- Restricting the canonical local section attached to `p` along `f` gives the canonical local
section attached to the restriction of `p`. -/
theorem freeGen_naturality {F : Cᵒᵖ ⥤ Type t} {U V : Cᵒᵖ} (f : U ⟶ V) (p : F.obj U) :
    (freePieceOf Osharp F).val.map f (freeGen Osharp p) = freeGen Osharp (F.map f p) :=
  (NatTrans.naturality_apply (freeGenNat Osharp F) f p).symm

/-- **The morphism out of `freePieceOf F` prescribed on the canonical local sections.** -/
noncomputable def freePieceDesc {F : Cᵒᵖ ⥤ Type t} (M : SheafOfModules.{t} (toRingCat J Osharp))
    (φ : F ⟶ M.val.presheaf ⋙ CategoryTheory.forget _) : freePieceOf Osharp F ⟶ M :=
  ⟨(PresheafOfModules.sheafifyHomEquiv' (𝟙 (toRingCat J Osharp).obj)
      (CategoryTheory.toSheafify J
        (PresheafOfModules.freeObj (R := (toRingCat J Osharp).obj) F).presheaf)
      M.isSheaf).symm (PresheafOfModules.freeObjDesc φ)⟩

/-- The composite of `freeToSheaf F` with `freePieceDesc M φ` is the morphism out of the free
presheaf of modules prescribed by `φ`. -/
theorem freePieceDesc_toSheaf {F : Cᵒᵖ ⥤ Type t} (M : SheafOfModules.{t} (toRingCat J Osharp))
    (φ : F ⟶ M.val.presheaf ⋙ CategoryTheory.forget _) :
    freeToSheaf Osharp F ≫ (freePieceDesc M φ).val = PresheafOfModules.freeObjDesc φ :=
  (PresheafOfModules.toPresheaf _).map_injective
    (PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom
      (𝟙 (toRingCat J Osharp).obj) _ M.isSheaf (PresheafOfModules.freeObjDesc φ))

/-- `freePieceDesc M φ` sends the canonical local section attached to `p` to `φ p`. -/
@[simp]
theorem freePieceDesc_gen {F : Cᵒᵖ ⥤ Type t} (M : SheafOfModules.{t} (toRingCat J Osharp))
    (φ : F ⟶ M.val.presheaf ⋙ CategoryTheory.forget _) {U : Cᵒᵖ} (p : F.obj U) :
    (freePieceDesc M φ).val.app U (freeGen Osharp p) = φ.app U p := by
  have h := congrArg (fun ψ : F ⟶ M.val.presheaf ⋙ CategoryTheory.forget _ => ψ.app U p)
    (PresheafOfModules.freeHomEquiv.apply_symm_apply φ)
  rwa [show PresheafOfModules.freeHomEquiv.symm φ =
      freeToSheaf Osharp F ≫ (freePieceDesc M φ).val from (freePieceDesc_toSheaf M φ).symm] at h

/-- **A morphism out of `freePieceOf F` is determined by its values on the canonical local
sections.** -/
theorem freePieceOf_hom_ext {F : Cᵒᵖ ⥤ Type t} {M : SheafOfModules.{t} (toRingCat J Osharp)}
    {f g : freePieceOf Osharp F ⟶ M}
    (h : ∀ (U : Cᵒᵖ) (p : F.obj U),
      f.val.app U (freeGen Osharp p) = g.val.app U (freeGen Osharp p)) :
    f = g := by
  have hpres : freeToSheaf Osharp F ≫ f.val = freeToSheaf Osharp F ≫ g.val := by
    refine PresheafOfModules.free_hom_ext ?_
    ext U p
    exact h U p
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Stacks.eq_of_forall_lift M.isSheaf.isSeparated (freeToSheaf Osharp F) x _ _ ?_
  intro Y r a ha
  show Stacks.sectionRestrict M.val r (f.val.app U x) =
    Stacks.sectionRestrict M.val r (g.val.app U x)
  have ha' : (freeToSheaf Osharp F).app Y a =
      Stacks.sectionRestrict (freePieceOf Osharp F).val r x := ha
  calc Stacks.sectionRestrict M.val r (f.val.app U x)
      = f.val.app Y (Stacks.sectionRestrict (freePieceOf Osharp F).val r x) :=
        (PresheafOfModules.naturality_apply f.val r x).symm
    _ = f.val.app Y ((freeToSheaf Osharp F).app Y a) := congrArg (fun z => f.val.app Y z) ha'.symm
    _ = g.val.app Y ((freeToSheaf Osharp F).app Y a) :=
        congrArg (fun ψ : PresheafOfModules.freeObj F ⟶ M.val => ψ.app Y a) hpres
    _ = g.val.app Y (Stacks.sectionRestrict (freePieceOf Osharp F).val r x) :=
        congrArg (fun z => g.val.app Y z) ha'
    _ = Stacks.sectionRestrict M.val r (g.val.app U x) :=
        PresheafOfModules.naturality_apply g.val r x

/-- The functoriality of `freePieceOf`. -/
noncomputable def freePieceMap {F G : Cᵒᵖ ⥤ Type t} (φ : F ⟶ G) :
    freePieceOf Osharp F ⟶ freePieceOf Osharp G :=
  freePieceDesc (freePieceOf Osharp G) (φ ≫ freeGenNat Osharp G)

/-- `freePieceMap φ` sends the canonical local section attached to `p` to the one attached to
`φ p`. -/
@[simp]
theorem freePieceMap_gen {F G : Cᵒᵖ ⥤ Type t} (φ : F ⟶ G) {U : Cᵒᵖ} (p : F.obj U) :
    (freePieceMap (Osharp := Osharp) φ).val.app U (freeGen Osharp p) =
      freeGen Osharp (φ.app U p) :=
  freePieceDesc_gen _ _ p

/-- `freePieceMap` preserves identities. -/
theorem freePieceMap_id (F : Cᵒᵖ ⥤ Type t) :
    freePieceMap (Osharp := Osharp) (𝟙 F) = 𝟙 _ :=
  freePieceOf_hom_ext fun U p => by rw [freePieceMap_gen]; rfl

/-- `freePieceMap` preserves composition. -/
theorem freePieceMap_comp {F G H : Cᵒᵖ ⥤ Type t} (φ : F ⟶ G) (ψ : G ⟶ H) :
    freePieceMap (Osharp := Osharp) (φ ≫ ψ) = freePieceMap φ ≫ freePieceMap ψ :=
  freePieceOf_hom_ext fun U p => by
    rw [freePieceMap_gen, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, freePieceMap_gen, freePieceMap_gen]
    rfl

/-- The composite of a morphism out of `freePieceOf F` with a morphism of sheaves of modules is
the morphism prescribed by the composite on the canonical sections. -/
theorem freePieceDesc_comp {F : Cᵒᵖ ⥤ Type t} {M N : SheafOfModules.{t} (toRingCat J Osharp)}
    (φ : F ⟶ M.val.presheaf ⋙ CategoryTheory.forget _) (g : M ⟶ N) :
    freePieceDesc M φ ≫ g =
      freePieceDesc N (φ ≫ Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map g.val)
        (CategoryTheory.forget _)) :=
  freePieceOf_hom_ext fun U p => by
    rw [freePieceDesc_gen, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, freePieceDesc_gen]
    rfl

end FreePiece

/-! ### The complex with zero differential on a family of presheaves -/

section ZeroDifferential

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

variable (Osharp) in
/-- The complex of `O`-modules with zero differential whose degree-`n` term is the
sheafification of the free `O`-module on `P n`. -/
noncomputable def freeOnPresheavesComplex (P : ℤ → (Cᵒᵖ ⥤ Type t)) :
    CochainComplex (SheafOfModules.{t} (toRingCat J Osharp)) ℤ where
  X n := freePieceOf Osharp (P n)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := zero_comp

/-- The degree-`n` term of `freeOnPresheavesComplex P` is `freePieceOf (P n)`. -/
@[simp] theorem freeOnPresheavesComplex_X (P : ℤ → (Cᵒᵖ ⥤ Type t)) (n : ℤ) :
    (freeOnPresheavesComplex Osharp P).X n = freePieceOf Osharp (P n) := rfl

/-- The differential of `freeOnPresheavesComplex P` is zero. -/
@[simp] theorem freeOnPresheavesComplex_d (P : ℤ → (Cᵒᵖ ⥤ Type t)) (n m : ℤ) :
    (freeOnPresheavesComplex Osharp P).d n m = 0 := rfl

variable (Osharp) in
/-- **The free complex `O[P]` with zero differential**, as a right differential graded
`(O, 0)`-module. -/
noncomputable def freeOnPresheaves (P : ℤ → (Cᵒᵖ ⥤ Type t)) :
    DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp) :=
  ofComplex (freeOnPresheavesComplex Osharp P)

/-- The inclusion of the closed sections into all the sections, as a morphism of presheaves of
sets. -/
noncomputable def closedSectionVal (Q : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp))
    (i : ℤ) : closedSection Q i ⟶ (Q.complex.X i).val.presheaf ⋙ CategoryTheory.forget _ where
  app _ := ↾fun x => x.1
  naturality _ _ _ := rfl

/-- The restriction of a morphism out of `O[P]` to the canonical generators: a morphism of
presheaves of sets from `P i` to the closed degree-`i` sections. -/
noncomputable def freeOnPresheavesToClosed (P : ℤ → (Cᵒᵖ ⥤ Type t))
    (Q : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp))
    (h : freeOnPresheaves Osharp P ⟶ Q) (i : ℤ) : P i ⟶ closedSection Q i where
  app U := ↾fun p => ⟨(h.toHomologicalComplex.f i).val.app U (freeGen Osharp p), by
    refine (homSections_congr (h.toHomologicalComplex.comm i (i + 1)) U _).trans ?_
    exact map_zero ((h.toHomologicalComplex.f (i + 1)).val.app U).hom⟩
  naturality {U V} f := by
    ext p
    refine Subtype.ext ?_
    change (h.toHomologicalComplex.f i).val.app V (freeGen Osharp ((P i).map f p)) =
      (Q.complex.X i).val.map f ((h.toHomologicalComplex.f i).val.app U (freeGen Osharp p))
    rw [← freeGen_naturality]
    exact PresheafOfModules.naturality_apply (h.toHomologicalComplex.f i).val f _

/-- The closed section `freeOnPresheavesToClosed P Q h i` attaches to `p` is the image under `h`
of the canonical local section attached to `p`. -/
@[simp] theorem freeOnPresheavesToClosed_app (P : ℤ → (Cᵒᵖ ⥤ Type t))
    (Q : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp))
    (h : freeOnPresheaves Osharp P ⟶ Q) (i : ℤ) (U : Cᵒᵖ) (p : (P i).obj U) :
    ((freeOnPresheavesToClosed P Q h i).app U p).1 =
      (h.toHomologicalComplex.f i).val.app U (freeGen Osharp p) := rfl

/-- The morphism out of `O[P]` prescribed by a family of closed generators. -/
noncomputable def freeOnPresheavesOfClosed (P : ℤ → (Cᵒᵖ ⥤ Type t))
    (Q : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp))
    (ψ : ∀ i, P i ⟶ closedSection Q i) : freeOnPresheaves Osharp P ⟶ Q :=
  homMk
    { f i := freePieceDesc (Q.complex.X i) (ψ i ≫ closedSectionVal Q i)
      comm' i j hij := by
        have hij' : i + 1 = j := hij
        subst hij'
        have key : freePieceDesc (Q.complex.X i) (ψ i ≫ closedSectionVal Q i) ≫
            Q.complex.d i (i + 1) = 0 := by
          refine freePieceOf_hom_ext fun U p => ?_
          rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
            freePieceDesc_gen]
          exact ((ψ i).app U p).2
        exact key.trans (zero_comp (f := freePieceDesc (Q.complex.X (i + 1))
          (ψ (i + 1) ≫ closedSectionVal Q (i + 1)))).symm }

/-- `freeOnPresheavesOfClosed P Q ψ` sends the canonical local section attached to `p` to the
closed section `ψ i p`. -/
@[simp] theorem freeOnPresheavesOfClosed_gen (P : ℤ → (Cᵒᵖ ⥤ Type t))
    (Q : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp))
    (ψ : ∀ i, P i ⟶ closedSection Q i) (i : ℤ) (U : Cᵒᵖ) (p : (P i).obj U) :
    ((freeOnPresheavesOfClosed P Q ψ).toHomologicalComplex.f i).val.app U (freeGen Osharp p) =
      ((ψ i).app U p).1 :=
  freePieceDesc_gen _ _ p

/-- **The universal property of `O[P]`**: a morphism out of it is a family of morphisms of
presheaves of sets from `P i` to the closed degree-`i` sections. -/
noncomputable def freeOnPresheavesHomEquiv (P : ℤ → (Cᵒᵖ ⥤ Type t))
    (Q : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp)) :
    (freeOnPresheaves Osharp P ⟶ Q) ≃ ∀ i, P i ⟶ closedSection Q i where
  toFun h i := freeOnPresheavesToClosed P Q h i
  invFun ψ := freeOnPresheavesOfClosed P Q ψ
  left_inv h := DifferentialGradedModule.Hom.ext fun i => freePieceOf_hom_ext fun U p =>
    freeOnPresheavesOfClosed_gen P Q (fun i => freeOnPresheavesToClosed P Q h i) i U p
  right_inv ψ := by
    funext i
    ext U p
    exact Subtype.ext (freeOnPresheavesOfClosed_gen P Q ψ i U p)

/-- `freeOnPresheavesToClosed` is natural in the target. -/
theorem freeOnPresheavesToClosed_comp (P : ℤ → (Cᵒᵖ ⥤ Type t))
    {Q Q' : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp)}
    (h : freeOnPresheaves Osharp P ⟶ Q) (k : Q ⟶ Q') (i : ℤ) :
    freeOnPresheavesToClosed P Q' (h ≫ k) i =
      freeOnPresheavesToClosed P Q h i ≫ (closedSectionMap k i).hom := by
  ext U p
  rfl

end ZeroDifferential

/-! ### The sheaf of graded sets generated by a family of presheaves -/

section GradedSet

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The disjoint union `U ↦ ⨿ₙ P n (U)` of a family of presheaves of sets. -/
def sigmaPresheaf (P : ℤ → (Cᵒᵖ ⥤ Type t)) : Cᵒᵖ ⥤ Type t where
  obj U := Σ n : ℤ, (P n).obj U
  map f := ↾fun x => ⟨x.1, (P x.1).map f x.2⟩
  map_id U := by
    ext ⟨n, p⟩
    · rfl
    · exact heq_of_eq ((P n).map_id_apply U p)
  map_comp {U V W} f g := by
    ext ⟨n, p⟩
    · rfl
    · exact heq_of_eq ((P n).map_comp_apply f g p)

/-- The degree of a local section of `⨿ₙ P n`. -/
def sigmaDegree (P : ℤ → (Cᵒᵖ ⥤ Type t)) :
    sigmaPresheaf P ⟶ (Functor.const Cᵒᵖ).obj (ULift.{t} ℤ) where
  app _ := ↾fun x => ⟨x.1⟩
  naturality _ _ _ := rfl

/-- The constant degree `i`. -/
def sigmaConstDegree (P : ℤ → (Cᵒᵖ ⥤ Type t)) (i : ℤ) :
    sigmaPresheaf P ⟶ (Functor.const Cᵒᵖ).obj (ULift.{t} ℤ) where
  app _ := ↾fun _ => ⟨i⟩
  naturality _ _ _ := rfl

/-- The inclusion of `P i` into `⨿ₙ P n`. -/
def sigmaIncl (P : ℤ → (Cᵒᵖ ⥤ Type t)) (i : ℤ) : P i ⟶ sigmaPresheaf P where
  app _ := ↾fun p => ⟨i, p⟩
  naturality _ _ _ := rfl

/-- A local section of `⨿ₙ P n` of degree `i`, read as a local section of `P i`. -/
def sigmaCast {P : ℤ → (Cᵒᵖ ⥤ Type t)} {U : Cᵒᵖ} (x : (sigmaPresheaf P).obj U) {i : ℤ}
    (h : x.1 = i) : (P i).obj U :=
  h ▸ x.2

/-- A local section of `⨿ₙ P n` of degree `i` is the pair of `i` and its reading in `P i`. -/
theorem sigmaCast_mk {P : ℤ → (Cᵒᵖ ⥤ Type t)} {U : Cᵒᵖ} (x : (sigmaPresheaf P).obj U) {i : ℤ}
    (h : x.1 = i) : (⟨i, sigmaCast x h⟩ : (sigmaPresheaf P).obj U) = x := by
  obtain ⟨n, p⟩ := x
  subst h
  rfl

/-- `sigmaCast` commutes with restriction. -/
theorem sigmaCast_map {P : ℤ → (Cᵒᵖ ⥤ Type t)} {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (sigmaPresheaf P).obj U) {i : ℤ} (h : x.1 = i) :
    sigmaCast ((sigmaPresheaf P).map f x) h = (P i).map f (sigmaCast x h) := by
  obtain ⟨n, p⟩ := x
  subst h
  rfl

/-- The fork of the degree of `⨿ₙ P n` and the constant degree `i` given by the inclusion of
`P i`. -/
def sigmaFork (P : ℤ → (Cᵒᵖ ⥤ Type t)) (i : ℤ) :
    Fork (sigmaDegree P) (sigmaConstDegree P i) :=
  Fork.ofι (sigmaIncl P i) rfl

/-- Equal local sections of `⨿ₙ P n` of degree `i` have equal readings in `P i`. -/
theorem sigmaCast_congr {P : ℤ → (Cᵒᵖ ⥤ Type t)} {U : Cᵒᵖ} {x y : (sigmaPresheaf P).obj U}
    (hxy : x = y) {i : ℤ} (hx : x.1 = i) (hy : y.1 = i) : sigmaCast x hx = sigmaCast y hy := by
  subst hxy; rfl

/-- Every local section in the image of a fork of the degree and the constant degree `i` has
degree `i`. -/
theorem sigmaFork_fst {P : ℤ → (Cᵒᵖ ⥤ Type t)} {i : ℤ}
    (s : Fork (sigmaDegree P) (sigmaConstDegree P i)) (U : Cᵒᵖ) (w : s.pt.obj U) :
    (s.ι.app U w).1 = i :=
  congrArg ULift.down (congrArg (fun φ => φ.app U w) s.condition)

/-- The morphism into `P i` induced by a fork. -/
def sigmaForkLift {P : ℤ → (Cᵒᵖ ⥤ Type t)} {i : ℤ}
    (s : Fork (sigmaDegree P) (sigmaConstDegree P i)) : s.pt ⟶ P i where
  app U := ↾fun w => sigmaCast (s.ι.app U w) (sigmaFork_fst s U w)
  naturality {U V} f := by
    ext w
    change sigmaCast (s.ι.app V (s.pt.map f w)) _ = (P i).map f (sigmaCast (s.ι.app U w) _)
    exact (sigmaCast_congr (NatTrans.naturality_apply s.ι f w) _
      (sigmaFork_fst s U w)).trans (sigmaCast_map f _ _)

/-- `P i` is the equalizer of the degree of `⨿ₙ P n` and the constant degree `i`. -/
def sigmaForkIsLimit (P : ℤ → (Cᵒᵖ ⥤ Type t)) (i : ℤ) : IsLimit (sigmaFork P i) :=
  Fork.IsLimit.mk _ (fun s => sigmaForkLift s)
    (fun s => by
      ext U w
      exact sigmaCast_mk _ _)
    (fun s m hm => by
      ext U w
      have h : (⟨i, m.app U w⟩ : (sigmaPresheaf P).obj U) = s.ι.app U w :=
        congrArg (fun φ => φ.app U w) hm
      change m.app U w = sigmaCast (s.ι.app U w) (sigmaFork_fst s U w)
      rw [← sigmaCast_congr h rfl (sigmaFork_fst s U w)]
      rfl)

variable [HasSheafify J (Type t)]

/-- **The sheaf of graded sets generated by a family of presheaves of sets**: the sheafification
of `U ↦ ⨿ₙ P n (U)`, a local section of `P n` having degree `n`. -/
noncomputable def gradedSetOfPresheaves (P : ℤ → (Cᵒᵖ ⥤ Type t)) : SheafOfGradedSets.{t} J where
  sheaf := (presheafToSheaf J (Type t)).obj (sigmaPresheaf P)
  degree := (presheafToSheaf J (Type t)).map (sigmaDegree P)

/-- The constant degree map of the sheafification is the sheafification of the constant degree
map. -/
theorem constantDegreeMap_gradedSetOfPresheaves (P : ℤ → (Cᵒᵖ ⥤ Type t)) (i : ℤ) :
    constantDegreeMap (gradedSetOfPresheaves (J := J) P) i =
      (presheafToSheaf J (Type t)).map (sigmaConstDegree P i) := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext J _ _ ((constantSheaf J (Type t)).obj (ULift.{t} ℤ)).property ?_
  have h : toSheafify J (sigmaPresheaf P) ≫
      (constantDegreeMap (gradedSetOfPresheaves (J := J) P) i).hom =
        sigmaConstDegree P i ≫ toSheafify J _ := by
    ext U x
    rfl
  exact h.trans (toSheafify_naturality J (sigmaConstDegree P i))

/-- **The sheaf of degree-`i` local sections of the sheaf of graded sets generated by `P` is the
sheafification of `P i`.** Sheafification preserves the equalizer of the degree and the constant
degree `i`, and in presheaves that equalizer is `P i`. -/
noncomputable def degreeFiberSheafIsoOfPresheaves (P : ℤ → (Cᵒᵖ ⥤ Type t)) (i : ℤ) :
    degreeFiberSheaf (gradedSetOfPresheaves (J := J) P) i ≅
      (presheafToSheaf J (Type t)).obj (P i) :=
  degreeFiberSheafIso _ i ≪≫
    eqToIso (by rw [constantDegreeMap_gradedSetOfPresheaves]; rfl) ≪≫
    (PreservesEqualizer.iso (presheafToSheaf J (Type t)) (sigmaDegree P)
      (sigmaConstDegree P i)).symm ≪≫
    (presheafToSheaf J (Type t)).mapIso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (sigmaForkIsLimit P i))

end GradedSet

/-! ### `O[P]` is the free differential graded `(O, 0)`-module on `T` -/

section Iso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [HasSheafify J (Type t)]

/-- The universal property of `O[P]` in sheaves of sets: a morphism out of it is a family of
morphisms from the sheaves of degree-`i` local sections of `T` to the closed degree-`i` local
sections. -/
noncomputable def freeOnPresheavesClosedEquiv (P : ℤ → (Cᵒᵖ ⥤ Type t))
    (Q : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp)) :
    (freeOnPresheaves Osharp P ⟶ Q) ≃
      ∀ i : ℤ, degreeFiberSheaf (gradedSetOfPresheaves (J := J) P) i ⟶ closedSectionSheaf Q i :=
  (freeOnPresheavesHomEquiv P Q).trans (Equiv.piCongrRight fun i =>
    ((sheafificationAdjunction J (Type t)).homEquiv (P i) (closedSectionSheaf Q i)).symm.trans
      ((degreeFiberSheafIsoOfPresheaves P i).homCongr (Iso.refl _)).symm)

/-- `freeOnPresheavesClosedEquiv P Q h i` is the precomposite with
`degreeFiberSheafIsoOfPresheaves P i` of the morphism of sheaves adjoint to
`freeOnPresheavesToClosed P Q h i`. -/
theorem freeOnPresheavesClosedEquiv_apply (P : ℤ → (Cᵒᵖ ⥤ Type t))
    (Q : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp))
    (h : freeOnPresheaves Osharp P ⟶ Q) (i : ℤ) :
    freeOnPresheavesClosedEquiv P Q h i =
      (degreeFiberSheafIsoOfPresheaves P i).hom ≫
        ((sheafificationAdjunction J (Type t)).homEquiv (P i) (closedSectionSheaf Q i)).symm
          (freeOnPresheavesToClosed P Q h i) :=
  rfl

/-- The universal property of `O[P]` in sheaves of sets is natural in the target. -/
theorem freeOnPresheavesClosedEquiv_comp (P : ℤ → (Cᵒᵖ ⥤ Type t))
    {Q Q' : DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp)} (k : Q ⟶ Q')
    (h : freeOnPresheaves Osharp P ⟶ Q) (i : ℤ) :
    freeOnPresheavesClosedEquiv P Q' (h ≫ k) i =
      freeOnPresheavesClosedEquiv P Q h i ≫ closedSectionMap k i := by
  have e1 : ((sheafificationAdjunction J (Type t)).homEquiv (P i) (closedSectionSheaf Q' i)).symm
      (freeOnPresheavesToClosed P Q' (h ≫ k) i) =
        ((sheafificationAdjunction J (Type t)).homEquiv (P i) (closedSectionSheaf Q i)).symm
          (freeOnPresheavesToClosed P Q h i) ≫ closedSectionMap k i :=
    (sheafificationAdjunction J (Type t)).homEquiv_naturality_right_symm
      (freeOnPresheavesToClosed P Q h i) (closedSectionMap k i)
  rw [freeOnPresheavesClosedEquiv_apply, freeOnPresheavesClosedEquiv_apply, e1, Category.assoc]

variable (Osharp) in
/-- **`O[P]` is the free differential graded `(O, 0)`-module on the sheaf of graded sets `T`
generated by `P`**, by the coYoneda lemma. -/
noncomputable def freeOnPresheavesIsoFreeDGModule (P : ℤ → (Cᵒᵖ ⥤ Type t)) :
    freeOnPresheaves Osharp P ≅
      freeDGModule (gradedSetOfPresheaves (J := J) P) (unitDGAlgebra Osharp) :=
  isoFreeDGModuleOfNatEquiv (gradedSetOfPresheaves P) (unitDGAlgebra Osharp)
    (freeOnPresheaves Osharp P) (fun Q => freeOnPresheavesClosedEquiv P Q)
    (fun k h i => freeOnPresheavesClosedEquiv_comp P k h i)

end Iso

/-! ### Goodness -/

section Good

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

omit [HasSheafify Y.J (Type w)] in
/-- **Goodness transports along an isomorphism**, at arbitrary universes of the two sites. -/
theorem isGoodToposBaseChange_of_iso {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}
    {P P' : DifferentialGradedModule.{w, w, w} A} (e : P ≅ P')
    (h : IsGoodToposBaseChange.{w, v₁, u₁} P) : IsGoodToposBaseChange.{w, v₁, u₁} P' := by
  refine ⟨RelativeTensor.IsGradedFlat.of_iso
      (GradedModule.ofDifferentialGradedIso e) h.1,
    RelativeTensor.IsKFlat.of_iso e h.2.1, ?_⟩
  intro X _ _ _ _ _ _ f B ψ hψ
  obtain ⟨⟨T, ⟨c⟩⟩, hflat⟩ := h.2.2 f B ψ hψ
  refine ⟨⟨T, ⟨c.ofIso (Functor.isoWhiskerLeft _ (coyoneda.mapIso e.op)).symm⟩⟩, ?_⟩
  intro T' c'
  exact hflat T' (c'.ofIso (Functor.isoWhiskerLeft _ (coyoneda.mapIso e.op)))

/-- **The free complex `O[P]` with zero differential on a family of presheaves of sets is good**:
it is the free differential graded `(O, 0)`-module on a sheaf of graded sets, which is good by
Tag 0FSG. -/
theorem freeOnPresheaves_isGoodToposBaseChange (P : ℤ → (Y.Cᵒᵖ ⥤ Type w)) :
    IsGoodToposBaseChange.{w, v₁, u₁} (freeOnPresheaves Y.O P) :=
  isGoodToposBaseChange_of_iso (freeOnPresheavesIsoFreeDGModule Y.O P).symm
    (freeDGModule_isGoodToposBaseChange (Y := Y) (A := unitDGAlgebra Y.O)
      (gradedSetOfPresheaves P))

end Good

end SheafOfModules

end
