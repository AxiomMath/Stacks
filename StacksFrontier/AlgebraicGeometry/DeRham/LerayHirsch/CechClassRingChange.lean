module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationCechClass
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalComparison
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalTransport
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalCup
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CechCupProductNaturality

/-!
# Total Čech complexes across a change of rings over the identity

Let `X` be a topological space, `𝒪` a sheaf of commutative rings on `X` and `U` an open covering of
`X`. For a complex `M` of `𝒪`-modules vanishing in negative degrees, the library's total Čech
complex `Tot(Č(U, M))` is identified with the elementwise total Čech complex of the sections of
`M` (`Stacks.Cech.RingChange.cechNatIso`), naturally in `M`, and under this identification the
augmentation of [Stacks, Tag 07M9] sends a global section `s` to the cochain `t ↦ s|_{U_t}`.

For a morphism of ringed spaces `h : (X, 𝒜) ⟶ (X, 𝒜')` which is the identity on the underlying
space, the sections of the pushforward `h_*M` of a complex of `𝒜`-modules are the sections of
`M`, read over `Γ(X, 𝒜')` (`Stacks.Cech.RingChange.pushSectionsIso`); so are the elementwise total
Čech complexes (`Stacks.Cech.RingChange.pushCechIso`), compatibly with the restriction cochains of
global sections. This is the change of rings `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` through which Čech
classes of `Ω^•_{X/S}` are compared with Čech classes of `Ω^•_{X/Y}` in the proof of
[Stacks, Tag 0FUM].

## Main definitions

* `Stacks.Cech.RingChange.natSections`, `Stacks.Cech.RingChange.cechNatIso`.
* `Stacks.Cech.RingChange.pushSectionsIso`, `Stacks.Cech.RingChange.pushCechIso`.

## Main results

* `Stacks.CategoryTheory.CechComplex.totalTo_naturality`: the comparison of total complexes is
  natural.
* `Stacks.Cech.RingChange.cechNatIso_hom_naturality`,
  `Stacks.Cech.RingChange.cechNatIso_hom_sectionsToTotalCech`.
* `Stacks.Cech.RingChange.pushSectionsIso_hom_naturality`,
  `Stacks.Cech.RingChange.totMap_pushSectionsIso_restrictTotS`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ComplexShape
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheafFunctor)
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.LinearCupProduct (PresheafModules cechCochains cechCochainsMap
  totalCechComplexFunctor ιTotalCech ιTotalCechTo ιTotalCechTo_eq totalCech_hom_ext
  cechCochainsMap_comp)

universe u

namespace Stacks.CategoryTheory.CechComplex

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype

variable {C : Type u} [Category.{u} C] [HasFiniteProducts C] {ι : Type u} (W : ι → C)
  {R : Type u} [CommRing R]

/-- A morphism of presheaves acts on the summands of the elementwise total complex
componentwise. -/
theorem totMap_totSingle {P Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ} (g : P ⟶ Q) (n : ℤ)
    (p b : ℕ) (h : (p : ℤ) + b = n) (y : Cochain W (P.X b) p) :
    totMap g n (totSingle W P n p b h y) = totSingle W Q n p b h (cochainMap W (g.f b) p y) := by
  funext i
  by_cases hi : i = ⟨(p, b), h⟩
  · subst hi
    simp only [totMap_apply, totSingle_apply_self]
  · rw [totMap_apply, totSingle_apply_ne W P n p b h y i hi,
      totSingle_apply_ne W Q n p b h _ i hi, map_zero]

/-- **The comparison of total complexes is natural** in the pair of complexes, for morphisms
compatible with the identifications in nonnegative degrees. -/
theorem totalTo_naturality {K K' : CochainComplex (PresheafModules.{u} C R) ℤ}
    {P P' : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ} (e : ∀ b : ℕ, K.X (b : ℤ) ≅ P.X b)
    (e' : ∀ b : ℕ, K'.X (b : ℤ) ≅ P'.X b) (f : K ⟶ K') (g : P ⟶ P')
    (hfg : ∀ b : ℕ, f.f b ≫ (e' b).hom = (e b).hom ≫ g.f b) (n : ℤ) :
    ((totalCechComplexFunctor W R).map f).f n ≫ totalTo W K' P' e' n =
      totalTo W K P e n ≫ (cechTotMap W P g).f n := by
  refine totalCech_hom_ext W R K fun p a hpa => ?_
  have key : ιTotalCechTo W R K p a n hpa ≫ ((totalCechComplexFunctor W R).map f).f n ≫
      totalTo W K' P' e' n =
      ιTotalCechTo W R K p a n hpa ≫ totalTo W K P e n ≫ (cechTotMap W P g).f n := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ totalTo W K' P' e' n)
      (Stacks.Cech.LinearCupProduct.ιTotalCechTo_totalCechComplexFunctor_map W R f p a n
        hpa))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (cechCochainsMap W R (f.f a) p ≫ ·) (ιTotalCechTo_totalTo W K' P' e' n p a
      hpa)).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ (cechTotMap W P g).f n)
      (ιTotalCechTo_totalTo W K P e n p a hpa)).symm
    obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ : (∃ b : ℕ, a = b) ∨ ∃ b : ℕ, a = Int.negSucc b := by
      rcases a with b | b
      · exact Or.inl ⟨b, rfl⟩
      · exact Or.inr ⟨b, rfl⟩
    · rw [summandTo_natCast, summandTo_natCast]
      refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
      show totSingle W P' n p b hpa ((cochainsIso W (P'.X b) p).hom
          ((cechCochainsMap W R (e' b).hom p).hom ((cechCochainsMap W R (f.f b) p).hom z))) =
        totMap g n (totSingle W P n p b hpa ((cochainsIso W (P.X b) p).hom
          ((cechCochainsMap W R (e b).hom p).hom z)))
      rw [totMap_totSingle]
      congr 1
      rw [← cochainsIso_hom_map]
      have h2 : (cechCochainsMap W R (e' b).hom p).hom ((cechCochainsMap W R (f.f b) p).hom z) =
          (cechCochainsMap W R (g.f b) p).hom ((cechCochainsMap W R (e b).hom p).hom z) := by
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
        exact congrArg (fun φ : cechCochains W R (K.X ↑b) p ⟶ cechCochains W R (P'.X b) p =>
          ConcreteCategory.hom φ z)
          ((cechCochainsMap_comp W R _ _ p).symm.trans
            ((congrArg (fun φ => cechCochainsMap W R φ p) (hfg b)).trans
              (cechCochainsMap_comp W R _ _ p)))
      rw [h2]
    · simp only [summandTo, Limits.comp_zero, Limits.zero_comp]
  rw [ιTotalCechTo_eq W R K p a n hpa] at key
  simpa only [Category.assoc] using key

end Stacks.CategoryTheory.CechComplex
namespace Stacks.Cech.RingChange

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- The sections over the opens of `X` of a complex of `𝒪`-modules, as a `ℤ`-indexed complex of
presheaves on the slice over `X`. -/
abbrev sectionsK (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) :=
  (Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).obj M

/-- **The sections of a complex of `𝒪`-modules in nonnegative degrees**, as an `ℕ`-indexed complex
of presheaves on the slice over `X`. -/
def natSections (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) :
    CochainComplex ((Over (⊤ : Opens X))ᵒᵖ ⥤ ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℕ where
  X b := (sectionsK O M).X b
  d i j := (sectionsK O M).d i j
  shape i j h := (sectionsK O M).shape _ _ (by
    simp only [ComplexShape.up_Rel] at h ⊢
    omega)
  d_comp_d' i j k _ _ := (sectionsK O M).d_comp_d _ _ _

/-- The identification of the two spellings of the sections in a nonnegative degree. -/
def natSectionsXIso (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) (b : ℕ) :
    (sectionsK O M).X (b : ℤ) ≅ (natSections O M).X b :=
  Iso.refl _

/-- The sections in nonnegative degrees, on morphisms. -/
def natSectionsMap {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ} (j : M ⟶ M') :
    natSections O M ⟶ natSections O M' where
  f b := ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).map j).f b
  comm' i k _ := ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).map j).comm _ _

/-- The sections in nonnegative degrees preserve composition of morphisms. -/
theorem natSectionsMap_comp {M M' M'' : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ}
    (j : M ⟶ M') (j' : M' ⟶ M'') :
    natSectionsMap O (j ≫ j') = natSectionsMap O j ≫ natSectionsMap O j' := by
  ext b : 1
  exact congrArg (fun φ => HomologicalComplex.Hom.f φ (b : ℤ))
    ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).map_comp j j')

variable {ι : Type u} (U : ι → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- The sections of a complex vanishing in negative degrees vanish in negative degrees. -/
theorem isZero_sectionsK_X (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (a : ℤ) (ha : a < 0) : IsZero ((sectionsK O M).X a) :=
  have := Stacks.Cohomology.CechDerived.preservesZeroMorphisms_sectionsPresheafFunctor.{u}
    (ringSheaf O) ⊤
  (sectionsPresheafFunctor (R := ringSheaf O) ⊤).map_isZero (hM a ha)

/-- The library's total Čech complex of a covering, at the spelling of the sections presheaves. -/
abbrev cechS := Stacks.Cech.Refinement.sectionsComplex O ⋙
  totalCechComplexFunctor (coverObject U hU) (SectionRing (ringSheaf O) ⊤)

/-- The library's total Čech complex of `M` is `cechS` applied to `M`. -/
theorem cech_obj_eq (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) :
    (Stacks.Cech.Hypercohomology.cech O U hU).obj M = (cechS O U hU).obj M :=
  congrArg (fun T => T.obj M) (Stacks.Cech.Refinement.totalCechComplexFunctor_eq O U hU)

/-- `cechNatIso` at the spelling of the sections presheaves. -/
def cechNatIsoS (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) :
    (cechS O U hU).obj M ≅ cechTot (coverObject U hU) (natSections O M) :=
  totalCechIso (coverObject U hU) (sectionsK O M) (natSections O M) (natSectionsXIso O M)
    (isZero_sectionsK_X O M hM) (fun b =>
      (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The library's total Čech complex of a complex vanishing in negative degrees is the
elementwise total Čech complex of its sections.** -/
def cechNatIso (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) :
    (Stacks.Cech.Hypercohomology.cech O U hU).obj M ≅
      cechTot (coverObject U hU) (natSections O M) :=
  eqToIso (cech_obj_eq O U hU M) ≪≫ cechNatIsoS O U hU M hM

/-- `cechNatIsoS` is natural in the complex. -/
theorem cechNatIsoS_hom_naturality {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ}
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (hM' : ∀ a : ℤ, a < 0 → IsZero (M'.X a))
    (j : M ⟶ M') :
    (cechS O U hU).map j ≫ (cechNatIsoS O U hU M' hM').hom =
      (cechNatIsoS O U hU M hM).hom ≫ cechTotMap (coverObject U hU) _ (natSectionsMap O j) :=
  HomologicalComplex.hom_ext _ _ fun n =>
    totalTo_naturality (coverObject U hU) (K := sectionsK O M) (K' := sectionsK O M')
      (P := natSections O M) (P' := natSections O M') (natSectionsXIso O M) (natSectionsXIso O M')
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).map j) (natSectionsMap O j)
      (fun b => (Category.comp_id _).trans (Category.id_comp _).symm) n

/-- `cechNatIso` is natural in the complex. -/
theorem cechNatIso_hom_naturality {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ}
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (hM' : ∀ a : ℤ, a < 0 → IsZero (M'.X a))
    (j : M ⟶ M') :
    (Stacks.Cech.Hypercohomology.cech O U hU).map j ≫ (cechNatIso O U hU M' hM').hom =
      (cechNatIso O U hU M hM).hom ≫ cechTotMap (coverObject U hU) _ (natSectionsMap O j) := by
  rw [Functor.congr_hom (Stacks.Cech.Refinement.totalCechComplexFunctor_eq O U hU) j]
  simp only [cechNatIso, Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  exact congrArg (eqToHom _ ≫ ·) (cechNatIsoS_hom_naturality O U hU hM hM' j)

/-- The Čech `0`-cochain `t ↦ x|_{U_t}` of a section `x` over the terminal object of a presheaf on
the slice over `X`. -/
def restrictCochainOver (F : (Over (⊤ : Opens X))ᵒᵖ ⥤ ModuleCat.{u} (SectionRing (ringSheaf O) ⊤))
    (x : F.obj (op (Over.mk (𝟙 ⊤)))) : Cochain (coverObject U hU) F 0 :=
  fun t => (F.map (Over.mkIdTerminal.from (inter (coverObject U hU) t)).op).hom x

/-- The cochain of a global section of a complex vanishing in negative degrees, placed in Čech
degree `0` of the elementwise total complex. -/
def restrictTotS (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) (n : ℕ)
    (s : (SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).obj (M.X n)) :
    TotX (coverObject U hU) (natSections O M) (n : ℤ) :=
  totSingle (coverObject U hU) (natSections O M) n 0 n (by simp)
    (restrictCochainOver O U hU ((natSections O M).X n)
      (((Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso (R := ringSheaf O) ⊤).inv.app
        (M.X n)).hom s))

/-- **The augmentation of [Stacks, Tag 07M9] restricts a global section**: under `cechNatIso` the
image of a global section `s` of `M^n` in the total Čech complex is the cochain `t ↦ s|_{U_t}` in
Čech degree `0`. -/
theorem cechNatIso_hom_sectionsToTotalCech (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (n : ℕ)
    (s : (SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).obj (M.X n)) :
    ((cechNatIso O U hU M hM).hom.f n).hom
        ((((Stacks.Cech.Linear.sectionsToTotalCech X (ringSheaf O) ⊤ U hU).app M).f n).hom s) =
      restrictTotS O U hU M n s := by
  show (totalTo (coverObject U hU) (sectionsK O M) (natSections O M) (natSectionsXIso O M)
      n).hom ((ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (sectionsK O M) 0
        (n : ℤ) n (by simp)).hom ((Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction
          (ringSheaf O) ⊤ U hU (M.X n)).hom s)) = _
  refine (ConcreteCategory.congr_hom (ιTotalCechTo_totalTo (coverObject U hU) (sectionsK O M)
    (natSections O M) (natSectionsXIso O M) n 0 n (by simp)) _).trans ?_
  show totSingle (coverObject U hU) (natSections O M) n 0 n _
      ((cochainsIso (coverObject U hU) ((natSections O M).X n) 0).hom
        ((cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
          (natSectionsXIso O M n).hom 0).hom
          ((Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction (ringSheaf O) ⊤ U hU
            (M.X n)).hom s))) = _
  refine congrArg (totSingle (coverObject U hU) (natSections O M) n 0 n _) (funext fun t => ?_)
  refine (cochainsIso_hom_apply _ _ 0 _ t).trans ?_
  refine (ConcreteCategory.congr_hom (Stacks.Cech.LinearCupProduct.cechCochainsMap_comp_π
    (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (natSectionsXIso O M n).hom 0 t) _).trans ?_
  exact ConcreteCategory.congr_hom (Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction_comp_π
    (ringSheaf O) ⊤ U hU (M.X n) t) s

end Stacks.Cech.RingChange

namespace Stacks.Cech.RingChange

open AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (baseRingedSpace)

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  {A A' : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
  (h : baseRingedSpace A ⟶ baseRingedSpace A') (hh : h.hom.base = 𝟙 X.carrier)

include hh in
/-- The preimage of an open under the underlying map of `h` is the open itself. -/
theorem map_obj_eq (V : Opens X.carrier) : (Opens.map h.hom.base).obj V = V := by
  rw [hh]
  rfl

/-- The pushforward of a complex along `h`. -/
abbrev pushC (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ) :
    CochainComplex (SheafOfModules.{u} (ringSheaf A')) ℤ :=
  ((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex _).obj M

/-- The ring map `Γ(X, 𝒜') ⟶ Γ(X, 𝒜)` of `h`. -/
abbrev globalHom : SectionRing (ringSheaf A') ⊤ →+* SectionRing (ringSheaf A) ⊤ :=
  (h.hom.c.app (op ⊤)).hom

include hh in
/-- **Sections of a pushforward along `h` are sections of the complex**, read over `Γ(X, 𝒜')`. -/
def pushSectionsLinearMap (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ) (b : ℕ)
    (W : Over (⊤ : Opens X.carrier)) :
    ((natSections A' (pushC h M)).X b).obj (op W) →ₗ[SectionRing (ringSheaf A') ⊤]
      ((restrictComplex (globalHom h) (natSections A M)).X b).obj (op W) where
  toFun x := ((M.X b).val.map (eqToHom (map_obj_eq h hh W.left).symm).op).hom x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    rw [RingHom.id_apply]
    have h1 : (r • x : ((natSections A' (pushC h M)).X b).obj (op W)) =
        (show ((pushC h M).X b).val.obj (op W.left) from
          ((ringSheaf A').obj.map (Over.mkIdTerminal.from W).left.op).hom r •
            (show ((pushC h M).X b).val.obj (op W.left) from x)) := rfl
    have h2 : ∀ (a : (ringSheaf A').obj.obj (op W.left))
        (y : ((pushC h M).X b).val.obj (op W.left)),
        a • y = (show (M.X b).val.obj (op ((Opens.map h.hom.base).obj W.left)) from
          (show (ringSheaf A).obj.obj (op ((Opens.map h.hom.base).obj W.left)) from
            (h.hom.c.app (op W.left)).hom a) •
          (show (M.X b).val.obj (op ((Opens.map h.hom.base).obj W.left)) from y)) :=
      fun _ _ => rfl
    let e := eqToHom (map_obj_eq h hh W.left).symm
    have h3 : ∀ y : ((restrictComplex (globalHom h) (natSections A M)).X b).obj (op W),
        (r • y : ((restrictComplex (globalHom h) (natSections A M)).X b).obj (op W)) =
        (show (M.X b).val.obj (op W.left) from
          ((ringSheaf A).obj.map (Over.mkIdTerminal.from W).left.op).hom (globalHom h r) •
            (show (M.X b).val.obj (op W.left) from y)) := fun _ => rfl
    rw [h1, h2]
    refine Eq.trans ?_ (h3 _).symm
    refine ((M.X b).val.map_smul e.op _ _).trans ?_
    congr 1
    have hn := ConcreteCategory.congr_hom
      (h.hom.c.naturality (Over.mkIdTerminal.from W).left.op) r
    change ((ringSheaf A).obj.map e.op).hom ((h.hom.c.app (op W.left)).hom
      (((ringSheaf A').obj.map (Over.mkIdTerminal.from W).left.op).hom r)) = _
    refine (congrArg ((ringSheaf A).obj.map e.op).hom hn).trans ?_
    change ((ringSheaf A).obj.map e.op).hom (((ringSheaf A).obj.map
      ((Opens.map h.hom.base).map (Over.mkIdTerminal.from W).left).op).hom
        ((h.hom.c.app (op ⊤)).hom r)) =
      ((ringSheaf A).obj.map (Over.mkIdTerminal.from W).left.op).hom ((h.hom.c.app (op ⊤)).hom r)
    exact (congrArg (fun φ => RingCat.Hom.hom φ ((h.hom.c.app (op ⊤)).hom r))
      ((ringSheaf A).obj.map_comp
        ((Opens.map h.hom.base).map (Over.mkIdTerminal.from W).left).op e.op)).symm

/-- Two restriction maps of a presheaf of modules on the opens composing to the same map agree. -/
theorem presheafOfModules_map_map {R : (Opens X.carrier)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{u} R) {U V W : (Opens X.carrier)ᵒᵖ} (g : U ⟶ V) (f : V ⟶ W)
    (k : U ⟶ W) (x : N.obj U) : N.map f (N.map g x) = N.map k x :=
  (N.map_comp_apply g f x).symm.trans (N.congr_map_apply (Subsingleton.elim _ _) x)

/-- An endomorphism of an open acts as the identity on a presheaf of modules on the opens. -/
theorem presheafOfModules_map_self {R : (Opens X.carrier)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{u} R) {U : (Opens X.carrier)ᵒᵖ} (k : U ⟶ U) (x : N.obj U) :
    N.map k x = x :=
  (N.congr_map_apply (Subsingleton.elim k (𝟙 U)) x).trans
    (ConcreteCategory.congr_hom (N.presheaf.map_id U) x)

include hh in
/-- **Sections of a pushforward along `h` are sections of the complex**, as a linear
equivalence. -/
def pushSectionsEquiv (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ) (b : ℕ)
    (W : Over (⊤ : Opens X.carrier)) :
    ((natSections A' (pushC h M)).X b).obj (op W) ≃ₗ[SectionRing (ringSheaf A') ⊤]
      ((restrictComplex (globalHom h) (natSections A M)).X b).obj (op W) where
  __ := pushSectionsLinearMap h hh M b W
  invFun y := ((M.X b).val.map (eqToHom (map_obj_eq h hh W.left)).op).hom y
  left_inv x := by
    change ((M.X b).val.map (eqToHom (map_obj_eq h hh W.left)).op).hom
      (((M.X b).val.map (eqToHom (map_obj_eq h hh W.left).symm).op).hom
        (show (M.X b).val.obj (op ((Opens.map h.hom.base).obj W.left)) from x)) = x
    exact (presheafOfModules_map_map (M.X b).val
      (eqToHom (map_obj_eq h hh W.left).symm).op (eqToHom (map_obj_eq h hh W.left)).op
      (𝟙 _) _).trans (presheafOfModules_map_self (M.X b).val (𝟙 _) _)
  right_inv y := by
    change ((M.X b).val.map (eqToHom (map_obj_eq h hh W.left).symm).op).hom
      (((M.X b).val.map (eqToHom (map_obj_eq h hh W.left)).op).hom
        (show (M.X b).val.obj (op W.left) from y)) = y
    exact (presheafOfModules_map_map (M.X b).val
      (eqToHom (map_obj_eq h hh W.left)).op (eqToHom (map_obj_eq h hh W.left).symm).op
      (𝟙 _) _).trans (presheafOfModules_map_self (M.X b).val (𝟙 _) _)

/-- `pushSectionsEquiv` is the restriction map along the equality `h⁻¹(W) = W`. -/
theorem pushSectionsEquiv_apply (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ) (b : ℕ)
    (W : Over (⊤ : Opens X.carrier)) (x : ((natSections A' (pushC h M)).X b).obj (op W)) :
    pushSectionsEquiv h hh M b W x =
      ((M.X b).val.map (eqToHom (map_obj_eq h hh W.left).symm).op).hom x :=
  rfl

/-- **Sections of a pushforward along `h` are sections of the complex**, as an isomorphism of
presheaves of `Γ(X, 𝒜')`-modules on the slice over `X`. -/
def pushSectionsIsoX (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ) (b : ℕ) :
    (natSections A' (pushC h M)).X b ≅ (restrictComplex (globalHom h) (natSections A M)).X b :=
  NatIso.ofComponents (fun W => (pushSectionsEquiv h hh M b W.unop).toModuleIso) (by
    intro W W' f
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change ((M.X b).val.map (eqToHom (map_obj_eq h hh W'.unop.left).symm).op).hom
        (((M.X b).val.map ((Opens.map h.hom.base).map f.unop.left).op).hom x) =
      ((M.X b).val.map f.unop.left.op).hom
        (((M.X b).val.map (eqToHom (map_obj_eq h hh W.unop.left).symm).op).hom x)
    exact (presheafOfModules_map_map (M.X b).val ((Opens.map h.hom.base).map f.unop.left).op
        (eqToHom (map_obj_eq h hh W'.unop.left).symm).op
        ((eqToHom (map_obj_eq h hh W.unop.left).symm).op ≫ f.unop.left.op) x).trans
      (presheafOfModules_map_map (M.X b).val (eqToHom (map_obj_eq h hh W.unop.left).symm).op
        f.unop.left.op _ x).symm)

/-- **The sections of a pushforward along `h` are the sections of the complex**, as an isomorphism
of complexes of presheaves of `Γ(X, 𝒜')`-modules. -/
def pushSectionsIso (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ) :
    natSections A' (pushC h M) ≅ restrictComplex (globalHom h) (natSections A M) :=
  HomologicalComplex.Hom.isoOfComponents (pushSectionsIsoX h hh M) (fun i j _ => by
    ext W x
    change ((M.d i j).val.app (op W.unop.left)).hom
        (((M.X i).val.map (eqToHom (map_obj_eq h hh W.unop.left).symm).op).hom x) =
      ((M.X j).val.map (eqToHom (map_obj_eq h hh W.unop.left).symm).op).hom
        (((M.d i j).val.app (op ((Opens.map h.hom.base).obj W.unop.left))).hom x)
    exact PresheafOfModules.naturality_apply (M.d i j).val
      (eqToHom (map_obj_eq h hh W.unop.left).symm).op x)

/-- `pushSectionsIso` is natural in the complex. -/
theorem pushSectionsIso_hom_naturality {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ}
    (j : M ⟶ M') :
    natSectionsMap A' (((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex _).map j) ≫
        (pushSectionsIso h hh M').hom =
      (pushSectionsIso h hh M).hom ≫
        (show restrictComplex (globalHom h) (natSections A M) ⟶
          restrictComplex (globalHom h) (natSections A M') from
          { f := fun b => Functor.whiskerRight ((natSectionsMap A j).f b)
              (ModuleCat.restrictScalars (globalHom h))
            comm' := fun i k _ => by
              ext W x
              exact ConcreteCategory.congr_hom
                (NatTrans.congr_app ((natSectionsMap A j).comm i k) W) x }) := by
  ext b W x
  show ((M'.X b).val.map (eqToHom (map_obj_eq h hh W.unop.left).symm).op).hom
      (((j.f b).val.app (op ((Opens.map h.hom.base).obj W.unop.left))).hom x) =
    ((j.f b).val.app (op W.unop.left)).hom
      (((M.X b).val.map (eqToHom (map_obj_eq h hh W.unop.left).symm).op).hom x)
  exact (PresheafOfModules.naturality_apply (j.f b).val
    (eqToHom (map_obj_eq h hh W.unop.left).symm).op x).symm

variable {ι : Type u} (U : ι → Opens X.carrier) (hU : ⊤ = ⨆ i, U i)

/-- **The elementwise total Čech complex of a pushforward along `h`** is that of the complex, with
its scalars restricted along `Γ(X, 𝒜') ⟶ Γ(X, 𝒜)`. -/
def pushCechIso (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ) :
    cechTot (coverObject U hU) (natSections A' (pushC h M)) ≅
      cechTot (coverObject U hU) (restrictComplex (globalHom h) (natSections A M)) :=
  cechTotMapIso (coverObject U hU) (pushSectionsIso h hh M)

/-- **The restriction cochain of a global section is compatible with the pushforward.** -/
theorem totMap_pushSectionsIso_restrictTotS
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (n : ℕ) (s : (SheafOfModules.evaluation.{u} (ringSheaf A) (op ⊤)).obj (M.X n)) :
    (totMap (pushSectionsIso h hh M).hom n (restrictTotS A' U hU (pushC h M) n s) :
      TotX (coverObject U hU) (natSections A M) n) = restrictTotS A U hU M n s := by
  refine (totMap_totSingle _ _ _ _ _ _ _).trans ?_
  refine congrArg (totSingle (coverObject U hU) _ n 0 n _) (funext fun t => ?_)
  show ((M.X n).val.map (eqToHom (map_obj_eq h hh (inter (coverObject U hU) t).left).symm).op).hom
      (((M.X n).val.map ((Opens.map h.hom.base).map
        (Over.mkIdTerminal.from (inter (coverObject U hU) t)).left).op).hom s) =
    ((M.X n).val.map (Over.mkIdTerminal.from (inter (coverObject U hU) t)).left.op).hom s
  exact presheafOfModules_map_map (M.X n).val _ _ _ s

end Stacks.Cech.RingChange
