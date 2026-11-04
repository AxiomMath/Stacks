module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ColimitsOfSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InjectiveSystemsOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites.MorphismOfSitesAndDescent

/-! # Cohomology of a colimit of sites with finite coverings: the cohomology diagram

The third of the four files on the cohomology of a colimit of sites with finite coverings
(see `CohomologyOfColimitOfFiniteSites.AbelianSystemsAndSections`). For an inverse system `D` of
sites with finite coverings, a system `F` of abelian sheaves on it and the colimit site `C` of
Stacks 09YL, it sets up the objects that Stacks 09YP compares:

* cohomology over an object of a small site and the canonical maps it carries along a continuous
  functor whose pushforward preserves injectives;
* the system of abelian sheaves, its injective resolutions levelwise (via Stacks 0EXZ), and the
  colimit sheaf `colim f_i^{-1}F_i` on `C`;
* the diagram of sections, and of cohomology groups `H^p(u_a(X), F_j)`, over the arrows
  `a : j ⟶ i` into a fixed index, the total site of the system with its finite coverings, and the
  presentation of the colimit sheaf as a left Kan extension.

The colimit statement itself, Stacks 09YP, is in `CohomologyOfColimitOfFiniteSites.CohomologyColimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous

universe v u w t s

namespace Stacks.WeakSites.ColimitSiteCohomology

/-! ### Cohomology over an object of a small site -/

/-- Sheafification of abelian sheaves is available for coefficients in any universe containing
the universe of the site. -/
local instance hasSheafifyAb {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A) :
    HasSheafify JA (Ab.{max w s}) := by
  have : Limits.PreservesFilteredColimitsOfSize.{w, w} (forget (Ab.{max w s})) :=
    Limits.preservesFilteredColimitsOfSize_shrink _
  infer_instance

/-- Abelian sheaves on a small site have enough injectives even when the coefficient universe
is enlarged beyond the universe of the site. -/
theorem enoughInjectivesAb {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A) :
    EnoughInjectives (Sheaf JA (Ab.{max w s})) := by
  let : EssentiallySmall.{max w s} A := essentiallySmallSelf A
  have : IsGrothendieckAbelian.{max w s} (Sheaf JA (Ab.{max w s})) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall JA (Ab.{max w s})
  exact IsGrothendieckAbelian.enoughInjectives

/-- Abelian sheaves on a small site have enough injectives, for coefficients in any universe
containing the universe of the site. -/
local instance enoughInjectivesAbInstance {A : Type w} [SmallCategory A]
    (JA : GrothendieckTopology A) :
    EnoughInjectives (Sheaf JA (Ab.{max w s})) := enoughInjectivesAb JA

/-- Sections over an object are additive. -/
local instance sections_additive {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A)
    (V : A) : (((sheafSections JA (Ab.{max w s})).obj (op V))).Additive where
  map_add := by intros; rfl

/-- Cohomology over equal objects is canonically identified. -/
def cohomologyCongr {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A) (p : ℕ)
    {V V' : A} (h : V = V') (P : Sheaf JA (Ab.{max w s})) :
    (((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P ⟶
      (((sheafSections JA (Ab.{max w s})).obj (op V')).rightDerived p).obj P :=
  eqToHom (by subst h; rfl)

/-- The map of complexes of sections over `V` induced by a degreewise map of complexes of
abelian sheaves into the restriction along `G`. -/
def sectionsComplexMap {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B} (G : A ⥤ B)
    (I : CochainComplex (Sheaf JA (Ab.{max w s})) ℕ)
    (J : CochainComplex (Sheaf JB (Ab.{max w s})) ℕ)
    (ψ : ∀ n : ℕ, (I.X n).obj ⟶ G.op ⋙ (J.X n).obj)
    (hψ : ∀ n n' : ℕ, (ComplexShape.up ℕ).Rel n n' →
      (I.d n n').hom ≫ ψ n' = ψ n ≫ Functor.whiskerLeft G.op (J.d n n').hom)
    (V : A) :
    (((sheafSections JA (Ab.{max w s})).obj (op V)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I ⟶
      (((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J where
  f n := (ψ n).app (op V)
  comm' n n' h := by
    have h' := congrArg (fun α => NatTrans.app α (op V)) (hψ n n' h)
    simpa using h'.symm

/-! The following two lemmas are the resolution bridge for maps of cohomology. A map from a
sheaf into the degree-zero cycles of a nonnegative complex of injectives lifts from any
injective resolution, and any two such lifts are homotopic. The target complex need not itself
be a resolution; this is essential for direct image, which is left exact but not exact. -/

private noncomputable def liftCochainZero {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0) : I.cocomplex.X 0 ⟶ T.X 0 := by
  letI : Injective (T.X 0) := hT 0
  let f' : ((CochainComplex.single₀ C).obj P).X 0 ⟶ T.X 0 := f
  exact Injective.factorThru f' (I.ι.f 0)

private theorem liftCochainZero_comm {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0) :
    I.ι.f 0 ≫ liftCochainZero I hT f = f := by
  let f' : ((CochainComplex.single₀ C).obj P).X 0 ⟶ T.X 0 := f
  show I.ι.f 0 ≫ Injective.factorThru f' (I.ι.f 0) = f'
  exact Injective.comp_factorThru f' (I.ι.f 0)

private noncomputable def liftCochainOne {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) : I.cocomplex.X 1 ⟶ T.X 1 := by
  letI : Injective (T.X 1) := hT 1
  have hzero : I.ι.f 0 ≫ liftCochainZero I hT f ≫ T.d 0 1 = 0 := by
    rw [← Category.assoc]
    rw [liftCochainZero_comm I hT f]
    exact hf
  exact (I.exact₀).descToInjective (liftCochainZero I hT f ≫ T.d 0 1) (by
    simpa [Category.assoc] using hzero)

private theorem liftCochainOne_comm {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) :
    I.cocomplex.d 0 1 ≫ liftCochainOne I hT f hf =
      liftCochainZero I hT f ≫ T.d 0 1 :=
  (I.exact₀).comp_descToInjective _ _

private noncomputable def liftCochainSucc {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (n : ℕ)
    (g : I.cocomplex.X n ⟶ T.X n)
    (g' : I.cocomplex.X (n + 1) ⟶ T.X (n + 1))
    (w : I.cocomplex.d n (n + 1) ≫ g' = g ≫ T.d n (n + 1)) :
    Σ' g'' : I.cocomplex.X (n + 2) ⟶ T.X (n + 2),
      I.cocomplex.d (n + 1) (n + 2) ≫ g'' = g' ≫ T.d (n + 1) (n + 2) := by
  letI : Injective (T.X (n + 2)) := hT (n + 2)
  exact ⟨(I.exact_succ n).descToInjective (g' ≫ T.d (n + 1) (n + 2)) (by
      simp [reassoc_of% w]),
    (I.exact_succ n).comp_descToInjective _ _⟩

private noncomputable def liftCochainMap {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) : I.cocomplex ⟶ T :=
  CochainComplex.mkHom _ _ (liftCochainZero I hT f) (liftCochainOne I hT f hf)
    (liftCochainOne_comm I hT f hf).symm
    (fun n ⟨g, g', w⟩ => ⟨(liftCochainSucc I hT n g g' w.symm).1,
      (liftCochainSucc I hT n g g' w.symm).2.symm⟩)

private theorem liftCochainMap_comm {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) :
    I.ι.f 0 ≫ (liftCochainMap I hT f hf).f 0 = f :=
  liftCochainZero_comm I hT f

private noncomputable def liftCochainHomotopyZeroZero {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : I.cocomplex ⟶ T)
    (h : I.ι ≫ f = 0) : I.cocomplex.X 1 ⟶ T.X 0 := by
  letI : Injective (T.X 0) := hT 0
  exact I.exact₀.descToInjective (f.f 0) (by
    have h0 := HomologicalComplex.congr_hom h 0
    simpa using h0)

private theorem liftCochainHomotopyZeroZero_comm {C : Type*} [Category C]
    [Abelian C] {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : I.cocomplex ⟶ T)
    (h : I.ι ≫ f = 0) :
    I.cocomplex.d 0 1 ≫ liftCochainHomotopyZeroZero I hT f h = f.f 0 :=
  I.exact₀.comp_descToInjective _ _

private noncomputable def liftCochainHomotopyZeroOne {C : Type*} [Category C]
    [Abelian C] {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : I.cocomplex ⟶ T)
    (h : I.ι ≫ f = 0) : I.cocomplex.X 2 ⟶ T.X 1 := by
  letI : Injective (T.X 1) := hT 1
  have hzero : I.cocomplex.d 0 1 ≫ liftCochainHomotopyZeroZero I hT f h = f.f 0 :=
    I.exact₀.comp_descToInjective _ _
  exact (I.exact_succ 0).descToInjective
    (f.f 1 - liftCochainHomotopyZeroZero I hT f h ≫ T.d 0 1) (by
      change I.cocomplex.d 0 1 ≫
        (f.f 1 - liftCochainHomotopyZeroZero I hT f h ≫ T.d 0 1) = 0
      calc
        _ = I.cocomplex.d 0 1 ≫ f.f 1 -
            (I.cocomplex.d 0 1 ≫ liftCochainHomotopyZeroZero I hT f h) ≫ T.d 0 1 := by
              simp only [Preadditive.comp_sub, Category.assoc]
        _ = f.f 0 ≫ T.d 0 1 - f.f 0 ≫ T.d 0 1 := by
              rw [hzero, ← HomologicalComplex.Hom.comm]
        _ = 0 := sub_self _)

private theorem liftCochainHomotopyZeroOne_comm {C : Type*} [Category C]
    [Abelian C] {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : I.cocomplex ⟶ T)
    (h : I.ι ≫ f = 0) :
    I.cocomplex.d 1 2 ≫ liftCochainHomotopyZeroOne I hT f h =
      f.f 1 - liftCochainHomotopyZeroZero I hT f h ≫ T.d 0 1 :=
  (I.exact_succ 0).comp_descToInjective _ _

private noncomputable def liftCochainHomotopyZeroSucc {C : Type*} [Category C]
    [Abelian C] {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : I.cocomplex ⟶ T) (n : ℕ)
    (g : I.cocomplex.X (n + 1) ⟶ T.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ T.X (n + 1))
    (h : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ T.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ T.X (n + 2) := by
  letI : Injective (T.X (n + 2)) := hT (n + 2)
  exact (I.exact_succ (n + 1)).descToInjective
    (f.f (n + 2) - g' ≫ T.d (n + 1) (n + 2)) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, h,
        Preadditive.add_comp, Category.assoc, Category.assoc,
        T.d_comp_d, comp_zero, add_zero, sub_self])

private theorem liftCochainHomotopyZeroSucc_comm {C : Type*} [Category C]
    [Abelian C] {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : I.cocomplex ⟶ T) (n : ℕ)
    (g : I.cocomplex.X (n + 1) ⟶ T.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ T.X (n + 1))
    (h : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ T.d n (n + 1)) :
    I.cocomplex.d (n + 2) (n + 3) ≫ liftCochainHomotopyZeroSucc I hT f n g g' h =
      f.f (n + 2) - g' ≫ T.d (n + 1) (n + 2) :=
  (I.exact_succ (n + 1)).comp_descToInjective _ _

private noncomputable def liftCochainHomotopyZero {C : Type*} [Category C]
    [Abelian C] {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f : I.cocomplex ⟶ T)
    (h : I.ι ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (liftCochainHomotopyZeroZero I hT f h)
    (liftCochainHomotopyZeroZero_comm I hT f h).symm
    (liftCochainHomotopyZeroOne I hT f h)
    (by
      rw [liftCochainHomotopyZeroOne_comm I hT f h]
      symm
      calc
        _ = (f.f 1 - liftCochainHomotopyZeroZero I hT f h ≫ T.d 0 1) +
              (liftCochainHomotopyZeroZero I hT f h ≫ T.d 0 1) := add_comm _ _
        _ = f.f 1 := sub_add_cancel _ _)
    (fun n ⟨g, g', w⟩ =>
      ⟨liftCochainHomotopyZeroSucc I hT f n g g' (by simp only [w, add_comm]), by
        rw [liftCochainHomotopyZeroSucc_comm I hT f n g g']
        symm
        calc
          _ = (f.f (n + 2) - g' ≫ T.d (n + 1) (n + 2)) +
                g' ≫ T.d (n + 1) (n + 2) := add_comm _ _
          _ = f.f (n + 2) := sub_add_cancel _ _⟩)

private noncomputable def liftCochainHomotopy {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) {f g : I.cocomplex ⟶ T}
    (hfg : I.ι ≫ f = I.ι ≫ g) : Homotopy f g := by
  exact Homotopy.equivSubZero.symm (liftCochainHomotopyZero I hT (f - g) (by
    rw [Preadditive.comp_sub, hfg, sub_self]))

private theorem liftCochainHomotopy_homologyMap_eq {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) {f g : I.cocomplex ⟶ T}
    (hfg : I.ι ≫ f = I.ι ≫ g) (p : ℕ) :
    HomologicalComplex.homologyMap f p = HomologicalComplex.homologyMap g p :=
  (liftCochainHomotopy I hT hfg).homologyMap_eq p

private theorem liftCochainHomotopy_homologyMap_eq_after_additive
    {C E : Type*} [Category C] [Abelian C] [Category E] [Abelian E]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) {f g : I.cocomplex ⟶ T}
    (hfg : I.ι ≫ f = I.ι ≫ g) (S : C ⥤ E) [S.Additive] (p : ℕ) :
    HomologicalComplex.homologyMap ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map f) p =
      HomologicalComplex.homologyMap ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map g) p :=
  (S.mapHomotopy (liftCochainHomotopy I hT hfg)).homologyMap_eq p

private theorem liftCochainMap_homologyMap_eq {C : Type*} [Category C] [Abelian C]
    {P : C} (I : InjectiveResolution P) {T : CochainComplex C ℕ}
    (hT : ∀ n, Injective (T.X n)) (f g : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) (hg : g ≫ T.d 0 1 = 0) (hfg : f = g) (p : ℕ) :
    HomologicalComplex.homologyMap (liftCochainMap I hT f hf) p =
      HomologicalComplex.homologyMap (liftCochainMap I hT g hg) p := by
  apply liftCochainHomotopy_homologyMap_eq I hT ?_ p
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    show I.ι.f 0 ≫ (liftCochainMap I hT f hf).f 0 =
      I.ι.f 0 ≫ (liftCochainMap I hT g hg).f 0
    rw [liftCochainMap_comm, liftCochainMap_comm, hfg]
  | succ n =>
    have hz : IsZero (((CochainComplex.single₀ C).obj P).X (n + 1)) := by
      apply HomologicalComplex.isZero_single_obj_X
      omega
    exact hz.eq_of_src _ _

private theorem sectionsComplexMap_homologyMap_eq_of_lifts
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) (hG : G.IsContinuous JA JB)
    (hL : (G.sheafPullback (Ab.{max w s}) JA JB).PreservesMonomorphisms)
    {P : Sheaf JA (Ab.{max w s})} (I : InjectiveResolution P)
    {J : CochainComplex (Sheaf JB (Ab.{max w s})) ℕ}
    (hJ : ∀ n, Injective (J.X n))
    {f g : I.cocomplex ⟶
      ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J}
    (hfg : I.ι ≫ f = I.ι ≫ g) (V : A) (p : ℕ) :
    HomologicalComplex.homologyMap
        (sectionsComplexMap G I.cocomplex J (fun n => (f.f n).hom)
          (by
            intro n n' _hn
            have h := congrArg (fun q => q.hom) (f.comm n n')
            change (I.cocomplex.d n n').hom ≫ (f.f n').hom =
              (f.f n).hom ≫ G.op.whiskerLeft (J.d n n').hom
            dsimp [Functor.sheafPushforwardContinuous] at h ⊢
            exact h.symm) V) p =
      HomologicalComplex.homologyMap
        (sectionsComplexMap G I.cocomplex J (fun n => (g.f n).hom)
          (by
            intro n n' _hn
            have h := congrArg (fun q => q.hom) (g.comm n n')
            change (I.cocomplex.d n n').hom ≫ (g.f n').hom =
              (g.f n).hom ≫ G.op.whiskerLeft (J.d n n').hom
            dsimp [Functor.sheafPushforwardContinuous] at h ⊢
            exact h.symm) V) p := by
  let : G.IsContinuous JA JB := hG
  let : (G.sheafPullback (Ab.{max w s}) JA JB).PreservesMonomorphisms := hL
  have : (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (G.sheafAdjunctionContinuous (Ab.{max w s}) JA JB)
  let S := (sheafSections JA (Ab.{max w s})).obj (op V)
  have hmap (q : I.cocomplex ⟶
      ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J) :
      sectionsComplexMap G I.cocomplex J (fun n => (q.f n).hom)
          (by
            intro n n' hn
            have h := congrArg (fun r => r.hom) (q.comm n n')
            show (I.cocomplex.d n n').hom ≫ (q.f n').hom =
              (q.f n).hom ≫ G.op.whiskerLeft (J.d n n').hom
            dsimp [Functor.sheafPushforwardContinuous] at h ⊢
            exact h.symm) V =
        (S.mapHomologicalComplex (ComplexShape.up ℕ)).map q := by
    ext n x
    rfl
  rw [hmap f, hmap g]
  exact (S.mapHomotopy (liftCochainHomotopy I (by
    intro n
    exact (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).injective_obj_of_injective
      (hJ n)) hfg)).homologyMap_eq p

/-- `IsCohomologyMap JA JB G φ V p m` says that `m` is the canonical map on cohomology
`Hᵖ(V, P) ⟶ Hᵖ(G V, Q)` determined by the functor `G` between sites and by the map of abelian
sheaves `φ : P ⟶ G_*Q`, written on underlying presheaves.

The map is pinned by asking for a lift of `φ` to injective resolutions of `P` and of `Q` and by
identifying `m` with the map induced on the homology of the complexes of sections; this is the
device of `Stacks.Cohomology.SpectralLimit.IsCohomologyMap`. Such a lift exists because the
restriction along a continuous functor of an injective abelian sheaf is injective, the
restriction being the right adjoint of an exact functor. -/
def IsCohomologyMap {A B : Type w} [SmallCategory A] [SmallCategory B]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B) (G : A ⥤ B)
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A) (p : ℕ)
    (m : ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).rightDerived p).obj Q)) : Prop :=
  ∃ (I : InjectiveResolution P) (J : InjectiveResolution Q)
      (ψ : ∀ n : ℕ, (I.cocomplex.X n).obj ⟶ G.op ⋙ (J.cocomplex.X n).obj)
      (hψ : ∀ n n' : ℕ, (ComplexShape.up ℕ).Rel n n' →
        (I.cocomplex.d n n').hom ≫ ψ n' =
          ψ n ≫ Functor.whiskerLeft G.op (J.cocomplex.d n n').hom),
    ((I.ι.f 0).hom ≫ ψ 0 = φ ≫ Functor.whiskerLeft G.op (J.ι.f 0).hom) ∧
      m = (I.isoRightDerivedObj ((sheafSections JA (Ab.{max w s})).obj (op V)) p).hom ≫
        HomologicalComplex.homologyMap
          (sectionsComplexMap G I.cocomplex J.cocomplex ψ hψ V) p ≫
        (J.isoRightDerivedObj
        ((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))) p).inv

private noncomputable def cohomologyMapOfLift
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (I : InjectiveResolution P) (J : InjectiveResolution Q)
    (lift : I.cocomplex ⟶
      ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex)
    (V : A) (p : ℕ) :
    ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).rightDerived p).obj Q) := by
  let ψ : ∀ n : ℕ, (I.cocomplex.X n).obj ⟶ G.op ⋙ (J.cocomplex.X n).obj :=
    fun n => (lift.f n).hom
  have hψ : ∀ n n' : ℕ, (ComplexShape.up ℕ).Rel n n' →
      (I.cocomplex.d n n').hom ≫ ψ n' =
        ψ n ≫ Functor.whiskerLeft G.op (J.cocomplex.d n n').hom := by
    intro n n' hn
    have h := congrArg (fun f => f.hom) (lift.comm n n')
    change (I.cocomplex.d n n').hom ≫ ψ n' =
      ψ n ≫ Functor.whiskerLeft G.op (J.cocomplex.d n n').hom
    exact h.symm
  exact (I.isoRightDerivedObj ((sheafSections JA (Ab.{max w s})).obj (op V)) p).hom ≫
    HomologicalComplex.homologyMap (sectionsComplexMap G I.cocomplex J.cocomplex ψ hψ V) p ≫
      (J.isoRightDerivedObj
        ((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))) p).inv

private theorem isCohomologyMap_cohomologyMapOfLift
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P ⟶ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)
    (I : InjectiveResolution P) (J : InjectiveResolution Q)
    (lift : I.cocomplex ⟶
      ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex)
    (h0 : (I.ι.f 0).hom ≫ (lift.f 0).hom =
      φ.hom ≫ Functor.whiskerLeft G.op (J.ι.f 0).hom)
    (V : A) (p : ℕ) :
    IsCohomologyMap JA JB G φ.hom V p (cohomologyMapOfLift G I J lift V p) := by
  refine ⟨I, J, (fun n => (lift.f n).hom), ?_, h0, rfl⟩
  intro n n' hn
  have h := congrArg (fun f => f.hom) (lift.comm n n')
  show (I.cocomplex.d n n').hom ≫ (lift.f n').hom =
    (lift.f n).hom ≫ Functor.whiskerLeft G.op (J.cocomplex.d n n').hom
  exact h.symm

private theorem cohomologyMapOfLift_eq
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (I I' : InjectiveResolution P) (J J' : InjectiveResolution Q)
    (f : I.cocomplex ⟶
      ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex)
    (g : I'.cocomplex ⟶
      ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J'.cocomplex)
    (φ : P ⟶ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)
    (hf : I.ι.f 0 ≫ f.f 0 = φ ≫
      (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (J.ι.f 0))
    (hg : I'.ι.f 0 ≫ g.f 0 = φ ≫
      (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (J'.ι.f 0))
    (V : A) (p : ℕ) :
    cohomologyMapOfLift G I J f V p = cohomologyMapOfLift G I' J' g V p := by
  let R := G.sheafPushforwardContinuous (Ab.{max w s}) JA JB
  let S := (sheafSections JA (Ab.{max w s})).obj (op V)
  let T := (sheafSections JB (Ab.{max w s})).obj (op (G.obj V))
  let q := InjectiveResolution.desc (𝟙 P) I' I
  let r := InjectiveResolution.desc (𝟙 Q) J' J
  have hq : I.ι.f 0 ≫ q.f 0 = I'.ι.f 0 := by
    simpa [q] using InjectiveResolution.desc_commutes_zero (𝟙 P) I' I
  have hr : J.ι.f 0 ≫ r.f 0 = J'.ι.f 0 := by
    simpa [r] using InjectiveResolution.desc_commutes_zero (𝟙 Q) J' J
  have hfg : I.ι ≫ (f ≫ (R.mapHomologicalComplex _).map r) = I.ι ≫ (q ≫ g) := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
      show I.ι.f 0 ≫ (f.f 0 ≫ R.map (r.f 0)) =
        I.ι.f 0 ≫ (q.f 0 ≫ g.f 0)
      rw [← Category.assoc, hf, Category.assoc, ← R.map_comp, hr,
        ← Category.assoc, hq, hg]
    | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)).eq_of_src _ _
  have hh := liftCochainHomotopy_homologyMap_eq_after_additive I
    (fun n => R.injective_obj_of_injective (J'.injective n)) hfg S p
  let HS := S.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor (Ab.{max w s}) (ComplexShape.up ℕ) p
  let HT := T.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor (Ab.{max w s}) (ComplexShape.up ℕ) p
  have hrmap : (S.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((R.mapHomologicalComplex (ComplexShape.up ℕ)).map r) =
      (T.mapHomologicalComplex (ComplexShape.up ℕ)).map r := by
    ext n
    rfl
  have hh' : HS.map f ≫ HT.map r = HS.map q ≫ HS.map g := by
    simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hh
    rw [hrmap] at hh
    exact hh
  have hq' : (I'.isoRightDerivedObj S p).hom = (I.isoRightDerivedObj S p).hom ≫ HS.map q := by
    have h := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 P) I I' q
      (by simpa using hq) S p
    rw [(S.rightDerived p).map_id P, Category.id_comp] at h
    exact h
  have hr' : (J.isoRightDerivedObj T p).inv = HT.map r ≫ (J'.isoRightDerivedObj T p).inv := by
    have h := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 Q) J J' r
      (by simpa using hr) T p
    rw [(T.rightDerived p).map_id Q, Category.comp_id] at h
    exact h
  show (I.isoRightDerivedObj S p).hom ≫ HS.map f ≫ (J.isoRightDerivedObj T p).inv =
    (I'.isoRightDerivedObj S p).hom ≫ HS.map g ≫ (J'.isoRightDerivedObj T p).inv
  rw [hr', ← Category.assoc (HS.map f), hh', hq']
  simp only [Category.assoc]

/-- A degreewise family of maps of presheaves into the restriction along `G`, compatible with the
differentials, as a map of cochain complexes of abelian sheaves into the restriction of the
target complex. This is the datum `IsCohomologyMap` is phrased with, packaged as the morphism of
complexes that `Stacks.Cohomology.RightDerivedEdge.edge_app_eq` consumes. -/
private def cochainMapOfComponents
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    (I : CochainComplex (Sheaf JA (Ab.{max w s})) ℕ)
    (J : CochainComplex (Sheaf JB (Ab.{max w s})) ℕ)
    (ψ : ∀ n : ℕ, (I.X n).obj ⟶ G.op ⋙ (J.X n).obj)
    (hψ : ∀ n n' : ℕ, (ComplexShape.up ℕ).Rel n n' →
      (I.d n n').hom ≫ ψ n' = ψ n ≫ Functor.whiskerLeft G.op (J.d n n').hom) :
    I ⟶ ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J where
  f n := ⟨ψ n⟩
  comm' n n' h := Sheaf.hom_ext (hψ n n' h).symm

private theorem isCohomologyMap_zero_comm
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A)
    {m : ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived 0).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).rightDerived 0).obj Q)}
    (hm : IsCohomologyMap JA JB G φ V 0 m) :
    ((sheafSections JA (Ab.{max w s})).obj (op V)).toRightDerivedZero.app P ≫ m =
      φ.app (op V) ≫
        ((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).toRightDerivedZero.app Q := by
  obtain ⟨I, J, ψ, hψ, h0, rfl⟩ := hm
  let L := (sheafSections JA (Ab.{max w s})).obj (op V)
  let R := (sheafSections JB (Ab.{max w s})).obj (op (G.obj V))
  let f := sectionsComplexMap G I.cocomplex J.cocomplex ψ hψ V
  have hcycles : I.toRightDerivedZero' L ≫ HomologicalComplex.cyclesMap f 0 =
      φ.app (op V) ≫ J.toRightDerivedZero' R := by
    apply (cancel_mono (HomologicalComplex.iCycles _ 0)).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    exact congrArg (fun a => a.app (op V)) h0
  rw [I.toRightDerivedZero_eq L, J.toRightDerivedZero_eq R]
  simp only [L, R, Category.assoc, Iso.inv_hom_id_assoc]
  show I.toRightDerivedZero' L ≫ HomologicalComplex.homologyπ _ 0 ≫
      HomologicalComplex.homologyMap f 0 ≫ (J.isoRightDerivedObj R 0).inv = _
  rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc, hcycles]
  simp only [Category.assoc]
  rfl

private theorem isCohomologyMap_unique
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A) (p : ℕ)
    {m n : ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).rightDerived p).obj Q)}
    (hm : IsCohomologyMap JA JB G φ V p m)
    (hn : IsCohomologyMap JA JB G φ V p n) : m = n := by
  obtain ⟨I, J, ψ, hψ, h0, rfl⟩ := hm
  obtain ⟨I', J', ψ', hψ', h0', rfl⟩ := hn
  exact cohomologyMapOfLift_eq G I I' J J'
    (cochainMapOfComponents G _ _ ψ hψ) (cochainMapOfComponents G _ _ ψ' hψ') ⟨φ⟩
    (by apply Sheaf.hom_ext; exact h0) (by apply Sheaf.hom_ext; exact h0') V p

private def cochainLiftOfSheafHom
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P ⟶ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)
    (I : InjectiveResolution P) (J : InjectiveResolution Q) :
    I.cocomplex ⟶
      ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex :=
  liftCochainMap I
    (fun n => (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).injective_obj_of_injective
      (J.injective n))
    (φ ≫ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (J.ι.f 0)) (by
      change (φ ≫ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (J.ι.f 0)) ≫
        (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (J.cocomplex.d 0 1) = 0
      rw [Category.assoc, ← Functor.map_comp, J.ι_f_zero_comp_complex_d,
        Functor.map_zero, comp_zero])

private theorem cochainLiftOfSheafHom_comm
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P ⟶ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)
    (I : InjectiveResolution P) (J : InjectiveResolution Q) :
    I.ι.f 0 ≫ (cochainLiftOfSheafHom G φ I J).f 0 =
      φ ≫ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (J.ι.f 0) :=
  liftCochainMap_comm _ _ _ _

private def canonicalCohomologyMap
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A) (p : ℕ) :
    ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).rightDerived p).obj Q) :=
  cohomologyMapOfLift G (InjectiveResolution.of P) (InjectiveResolution.of Q)
    (cochainLiftOfSheafHom G ⟨φ⟩ (InjectiveResolution.of P) (InjectiveResolution.of Q)) V p

private theorem isCohomologyMap_canonical
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A) (p : ℕ) :
    IsCohomologyMap JA JB G φ V p (canonicalCohomologyMap G φ V p) :=
  isCohomologyMap_cohomologyMapOfLift G ⟨φ⟩ _ _ _
    (congrArg (fun f => f.hom) (cochainLiftOfSheafHom_comm G ⟨φ⟩
      (InjectiveResolution.of P) (InjectiveResolution.of Q))) V p

private theorem isCohomologyMap_iff_eq_canonical
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A) (p : ℕ)
    (m : ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).rightDerived p).obj Q)) :
    IsCohomologyMap JA JB G φ V p m ↔ m = canonicalCohomologyMap G φ V p := by
  constructor
  · exact fun h => isCohomologyMap_unique G φ V p h (isCohomologyMap_canonical G φ V p)
  · rintro rfl
    exact isCohomologyMap_canonical G φ V p

private theorem canonicalCohomologyMap_comp
    {A B C : Type w} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    {JC : GrothendieckTopology C}
    (G : A ⥤ B) (H : B ⥤ C) [G.IsContinuous JA JB] [H.IsContinuous JB JC]
    [(G ⋙ H).IsContinuous JA JC]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    [(H.sheafPushforwardContinuous (Ab.{max w s}) JB JC).PreservesInjectiveObjects]
    [((G ⋙ H).sheafPushforwardContinuous (Ab.{max w s}) JA JC).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    {R : Sheaf JC (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (χ : Q.obj ⟶ H.op ⋙ R.obj) (V : A) (p : ℕ) :
    canonicalCohomologyMap (G ⋙ H) (φ ≫ Functor.whiskerLeft G.op χ) V p =
      canonicalCohomologyMap G φ V p ≫ canonicalCohomologyMap H χ (G.obj V) p := by
  apply isCohomologyMap_unique (G ⋙ H) (φ ≫ Functor.whiskerLeft G.op χ) V p
    (isCohomologyMap_canonical _ _ _ _)
  let I := InjectiveResolution.of P
  let J := InjectiveResolution.of Q
  let K := InjectiveResolution.of R
  let f := cochainLiftOfSheafHom G ⟨φ⟩ I J
  let g := cochainLiftOfSheafHom H ⟨χ⟩ J K
  let RG := G.sheafPushforwardContinuous (Ab.{max w s}) JA JB
  let RH := H.sheafPushforwardContinuous (Ab.{max w s}) JB JC
  let fg := f ≫ (RG.mapHomologicalComplex (ComplexShape.up ℕ)).map g
  let ψ : ∀ n, (I.cocomplex.X n).obj ⟶ (G ⋙ H).op ⋙ (K.cocomplex.X n).obj :=
    fun n => (fg.f n).hom
  have hψ : ∀ n n', (ComplexShape.up ℕ).Rel n n' →
      (I.cocomplex.d n n').hom ≫ ψ n' =
        ψ n ≫ Functor.whiskerLeft (G ⋙ H).op (K.cocomplex.d n n').hom := by
    intro n n' hn
    exact (congrArg (fun f => f.hom) (fg.comm n n')).symm
  have hf : (I.ι.f 0).hom ≫ (f.f 0).hom =
      φ ≫ Functor.whiskerLeft G.op (J.ι.f 0).hom :=
    congrArg (fun f => f.hom) (cochainLiftOfSheafHom_comm G ⟨φ⟩ I J)
  have hg : (J.ι.f 0).hom ≫ (g.f 0).hom =
      χ ≫ Functor.whiskerLeft H.op (K.ι.f 0).hom :=
    congrArg (fun f => f.hom) (cochainLiftOfSheafHom_comm H ⟨χ⟩ J K)
  have hzero : (I.ι.f 0).hom ≫ ψ 0 =
      (φ ≫ Functor.whiskerLeft G.op χ) ≫
        Functor.whiskerLeft (G ⋙ H).op (K.ι.f 0).hom := by
    show (I.ι.f 0).hom ≫ (f.f 0).hom ≫ Functor.whiskerLeft G.op (g.f 0).hom = _
    rw [← Category.assoc, hf, Category.assoc, ← Functor.whiskerLeft_comp, hg,
      Functor.whiskerLeft_comp, Category.assoc]
    rfl
  refine ⟨I, K, ψ, hψ, hzero, ?_⟩
  let S := (sheafSections JA (Ab.{max w s})).obj (op V)
  let T := (sheafSections JB (Ab.{max w s})).obj (op (G.obj V))
  let U := (sheafSections JC (Ab.{max w s})).obj (op (H.obj (G.obj V)))
  have hfg : sectionsComplexMap (G ⋙ H) I.cocomplex K.cocomplex ψ hψ V =
      (S.mapHomologicalComplex (ComplexShape.up ℕ)).map f ≫
        (T.mapHomologicalComplex (ComplexShape.up ℕ)).map g := by
    ext n
    rfl
  show ((I.isoRightDerivedObj S p).hom ≫
      HomologicalComplex.homologyMap ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map f) p ≫
        (J.isoRightDerivedObj T p).inv) ≫
    ((J.isoRightDerivedObj T p).hom ≫
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map g) p ≫
        (K.isoRightDerivedObj U p).inv) = _
  rw [hfg, HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private theorem isCohomologyMap_id
    {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A)
    (P : Sheaf JA (Ab.{max w s})) (V : A) (p : ℕ) :
    IsCohomologyMap JA JA (𝟭 A) (𝟙 P.obj) V p (𝟙 _) := by
  let I := InjectiveResolution.of P
  let ψ : ∀ n, (I.cocomplex.X n).obj ⟶ (𝟭 A).op ⋙ (I.cocomplex.X n).obj :=
    fun n => 𝟙 _
  have hψ : ∀ n n', (ComplexShape.up ℕ).Rel n n' →
      (I.cocomplex.d n n').hom ≫ ψ n' =
        ψ n ≫ Functor.whiskerLeft (𝟭 A).op (I.cocomplex.d n n').hom := by
    intro n n' hn
    simp only [ψ, Category.id_comp, Category.comp_id]
    rfl
  refine ⟨I, I, ψ, hψ, ?_, ?_⟩
  · simp only [ψ, Category.id_comp, Category.comp_id]
    rfl
  · have h : sectionsComplexMap (𝟭 A) I.cocomplex I.cocomplex ψ hψ V = 𝟙 _ := by
      ext n
      rfl
    rw [h, HomologicalComplex.homologyMap_id]
    let e := I.isoRightDerivedObj ((sheafSections JA (Ab.{max w s})).obj (op V)) p
    show 𝟙 _ = e.hom ≫ 𝟙 _ ≫ e.inv
    rw [Category.id_comp, Iso.hom_inv_id]

private def cohomologyMapTo
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A) (W : B) (h : G.obj V = W) (p : ℕ) :
    ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op W)).rightDerived p).obj Q) :=
  canonicalCohomologyMap G φ V p ≫ cohomologyCongr JB p h Q

private theorem cohomologyMapTo_congr
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G G' : A ⥤ B) [G.IsContinuous JA JB] [G'.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    [(G'.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (φ' : P.obj ⟶ G'.op ⋙ Q.obj)
    (e : G = G')
    (he : φ ≫ eqToHom (congrArg (fun H : A ⥤ B => H.op ⋙ Q.obj) e) = φ')
    (V : A) (W : B) (h : G.obj V = W) (h' : G'.obj V = W) (p : ℕ) :
    cohomologyMapTo G φ V W h p = cohomologyMapTo G' φ' V W h' p := by
  subst G'
  simp only [eqToHom_refl, Category.comp_id] at he
  subst φ'
  rfl

private theorem cohomologyMapTo_comp
    {A B C : Type w} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    {JC : GrothendieckTopology C}
    (G : A ⥤ B) (H : B ⥤ C) [G.IsContinuous JA JB] [H.IsContinuous JB JC]
    [(G ⋙ H).IsContinuous JA JC]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    [(H.sheafPushforwardContinuous (Ab.{max w s}) JB JC).PreservesInjectiveObjects]
    [((G ⋙ H).sheafPushforwardContinuous (Ab.{max w s}) JA JC).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    {R : Sheaf JC (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (χ : Q.obj ⟶ H.op ⋙ R.obj)
    (V : A) (W : B) (Z : C) (h : G.obj V = W) (h' : H.obj W = Z) (p : ℕ) :
    cohomologyMapTo G φ V W h p ≫ cohomologyMapTo H χ W Z h' p =
      cohomologyMapTo (G ⋙ H) (φ ≫ Functor.whiskerLeft G.op χ) V Z
        ((congrArg H.obj h).trans h') p := by
  subst W
  subst Z
  simpa only [cohomologyMapTo, cohomologyCongr, eqToHom_refl, Category.comp_id]
    using (canonicalCohomologyMap_comp G H φ χ V p).symm

private theorem pushforward_id_preservesInjectives
    {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A) :
    ((𝟭 A).sheafPushforwardContinuous (Ab.{max w s}) JA JA).PreservesInjectiveObjects := by
  refine ⟨fun {P} hP => ?_⟩
  exact Injective.of_iso ((Functor.sheafPushforwardContinuousId (Ab.{max w s}) JA).app P).symm hP

private theorem pushforward_comp_preservesInjectives
    {A B C : Type w} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    {JC : GrothendieckTopology C}
    (G : A ⥤ B) (H : B ⥤ C) [G.IsContinuous JA JB] [H.IsContinuous JB JC]
    [(G ⋙ H).IsContinuous JA JC]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    [(H.sheafPushforwardContinuous (Ab.{max w s}) JB JC).PreservesInjectiveObjects] :
    ((G ⋙ H).sheafPushforwardContinuous (Ab.{max w s}) JA JC).PreservesInjectiveObjects := by
  refine ⟨fun {P} hP => ?_⟩
  exact (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).injective_obj_of_injective
    ((H.sheafPushforwardContinuous (Ab.{max w s}) JB JC).injective_obj_of_injective hP)

private theorem cohomologyMapTo_id
    {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A)
    [((𝟭 A).sheafPushforwardContinuous (Ab.{max w s}) JA JA).PreservesInjectiveObjects]
    (P : Sheaf JA (Ab.{max w s})) (V : A) (p : ℕ) :
    cohomologyMapTo (𝟭 A) (𝟙 P.obj) V V rfl p = 𝟙 _ := by
  simp only [cohomologyMapTo, cohomologyCongr, eqToHom_refl, Category.comp_id]
  exact isCohomologyMap_unique (𝟭 A) (𝟙 P.obj) V p
    (isCohomologyMap_canonical _ _ _ _) (isCohomologyMap_id JA P V p)

private theorem cohomologyMapTo_isCohomologyMap
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A) (W : B) (h : G.obj V = W) (p : ℕ) :
    IsCohomologyMap JA JB G φ V p
      (cohomologyMapTo G φ V W h p ≫ cohomologyCongr JB p h.symm Q) := by
  subst W
  simpa only [cohomologyMapTo, cohomologyCongr, eqToHom_refl, Category.comp_id]
    using isCohomologyMap_canonical G φ V p

private theorem exists_isCohomologyMap_of_sheafHom
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B) (G : A ⥤ B)
    (hG : G.IsContinuous JA JB)
    (hL : (G.sheafPullback (Ab.{max w s}) JA JB).PreservesMonomorphisms)
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P ⟶ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)
    (V : A) (p : ℕ) :
    ∃ m, IsCohomologyMap JA JB G φ.hom V p m := by
  let : G.IsContinuous JA JB := hG
  let : (G.sheafPullback (Ab.{max w s}) JA JB).PreservesMonomorphisms := hL
  let adj : G.sheafPullback (Ab.{max w s}) JA JB ⊣
      G.sheafPushforwardContinuous (Ab.{max w s}) JA JB :=
    G.sheafAdjunctionContinuous (Ab.{max w s}) JA JB
  let : EnoughInjectives (Sheaf JA (Ab.{max w s})) := enoughInjectivesAb JA
  let : EnoughInjectives (Sheaf JB (Ab.{max w s})) := enoughInjectivesAb JB
  let I : InjectiveResolution P := InjectiveResolution.of P
  let J : InjectiveResolution Q := InjectiveResolution.of Q
  have : (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let T :=
    ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex
  have hT : ∀ n, Injective (T.X n) := by
    intro n
    exact (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).injective_obj_of_injective
      (J.injective n)
  have hsingle : Q = ((CochainComplex.single₀ (Sheaf JB (Ab.{max w s}))).obj Q).X 0 := by
    rfl
  let f : P ⟶ T.X 0 :=
    φ ≫ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map
      (eqToHom hsingle ≫ J.ι.f 0)
  have hι : J.ι.f 0 ≫ J.cocomplex.d 0 1 = 0 := J.ι_f_zero_comp_complex_d
  have hηd : (eqToHom hsingle ≫ J.ι.f 0) ≫ J.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc, hι, comp_zero]
  have hf : f ≫ T.d 0 1 = 0 := by
    show φ ≫ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map
      (eqToHom hsingle ≫ J.ι.f 0) ≫
        (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (J.cocomplex.d 0 1) = 0
    rw [← Functor.map_comp, hηd]
    rw [Functor.map_zero, comp_zero]
  let lift := liftCochainMap I hT f hf
  let ψ : ∀ n : ℕ, (I.cocomplex.X n).obj ⟶ G.op ⋙ (J.cocomplex.X n).obj :=
    fun n => (lift.f n).hom
  have hψ : ∀ n n' : ℕ, (ComplexShape.up ℕ).Rel n n' →
      (I.cocomplex.d n n').hom ≫ ψ n' =
        ψ n ≫ Functor.whiskerLeft G.op (J.cocomplex.d n n').hom := by
    intro n n' hn
    have h := congrArg (fun f : I.cocomplex.X n ⟶ T.X n' => f.hom) (lift.comm n n')
    show (I.cocomplex.d n n').hom ≫ ψ n' =
      ψ n ≫ Functor.whiskerLeft G.op (J.cocomplex.d n n').hom
    exact h.symm
  have h0 : (I.ι.f 0).hom ≫ ψ 0 = φ.hom ≫ Functor.whiskerLeft G.op (J.ι.f 0).hom := by
    have hLift : (I.ι.f 0).hom ≫ ψ 0 = f.hom := by
      dsimp [T, Functor.sheafPushforwardContinuous]
      simpa [ψ] using congrArg (fun g => g.hom) (liftCochainMap_comm I hT f hf)
    have hF : f.hom = φ.hom ≫ Functor.whiskerLeft G.op (J.ι.f 0).hom := by
      cases hsingle
      ext U
      rfl
    exact hLift.trans hF
  refine ⟨(I.isoRightDerivedObj ((sheafSections JA (Ab.{max w s})).obj (op V)) p).hom ≫
    HomologicalComplex.homologyMap (sectionsComplexMap G I.cocomplex J.cocomplex ψ hψ V) p ≫
      (J.isoRightDerivedObj
        ((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))) p).inv,
    I, J, ψ, hψ, h0, rfl⟩

/-! ### The system of abelian sheaves and the colimit sheaf -/

/-- The inverse-image transition `φ_a : f_a⁻¹F_j ⟶ F_k` of a system of abelian sheaves
(Tag 0EXZ), in adjoint form `F_j ⟶ f_{a,*}F_k` and on underlying presheaves. -/
def transition (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) {j k : D.I} (a : k ⟶ j) :
    (F.obj j).obj ⟶ (D.u a).op ⋙ (F.obj k).obj :=
  (((InverseSystemOfFiniteSites.abelianSheafAdjunction.{v, u, w, t} D a).homEquiv (F.obj j)
    (F.obj k)) (F.map a)).hom

private theorem transition_id
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    transition D F (𝟙 i) =
      ((InverseSystemOfFiniteSites.abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app
        (F.obj i)).hom := by
  have h : F.map (𝟙 i) =
      (InverseSystemOfFiniteSites.abelianSheafPullbackIdIso.{v, u, w, t} D i).hom.app
        (F.obj i) := by
    rw [← cancel_epi
      ((InverseSystemOfFiniteSites.abelianSheafPullbackIdIso.{v, u, w, t} D i).inv.app
        (F.obj i))]
    rw [F.map_id, Iso.inv_hom_id_app]
    rfl
  dsimp only [transition]
  rw [h]
  have hunit := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (InverseSystemOfFiniteSites.abelianSheafAdjunction.{v, u, w, t} D (𝟙 i))
    (Adjunction.id.ofNatIsoRight
      (InverseSystemOfFiniteSites.abelianSheafPushforwardIdIso.{v, u, w, t} D i))
    (F.obj i)
  dsimp only [InverseSystemOfFiniteSites.abelianSheafPullbackIdIso]
  refine (congrArg (fun f => f.hom) hunit).trans ?_
  ext V x
  rfl

private theorem homEquiv_leftAdjointUniq_inv_comp
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) (b : L' ⊣ R)
    {X : A} {Y : B} (f : L.obj X ⟶ Y) :
    b.homEquiv X Y ((a.leftAdjointUniq b).inv.app X ≫ f) = a.homEquiv X Y f := by
  rw [Adjunction.leftAdjointUniq_inv_app, b.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

private theorem transition_comp
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i j k : D.I} (a : k ⟶ j) (b : j ⟶ i) :
    transition D F (a ≫ b) =
      transition D F b ≫ Functor.whiskerLeft (D.u b).op (transition D F a) ≫
        ((InverseSystemOfFiniteSites.abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app
          (F.obj k)).hom := by
  show (((InverseSystemOfFiniteSites.abelianSheafAdjunction.{v, u, w, t} D (a ≫ b)).homEquiv _ _)
    (F.map (a ≫ b))).hom = _
  rw [← F.map_comp a b]
  dsimp only [InverseSystemOfFiniteSites.abelianSheafPullbackCompIso]
  rw [homEquiv_leftAdjointUniq_inv_comp, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  show ((((InverseSystemOfFiniteSites.abelianSheafAdjunction.{v, u, w, t} D b).homEquiv _ _)
    (((InverseSystemOfFiniteSites.abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _)
      ((InverseSystemOfFiniteSites.abelianSheafPullback.{v, u, w, t} D a).map (F.map b) ≫
        F.map a))) ≫
    (InverseSystemOfFiniteSites.abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app
      (F.obj k)).hom = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rfl

private theorem pushforward_eqToIso_hom
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    {G G' : A ⥤ B} [G.IsContinuous JA JB] [G'.IsContinuous JA JB]
    (e : G = G') (P : Sheaf JB (Ab.{max w s})) :
    ((Functor.sheafPushforwardContinuousIso (eqToIso e)
      (Ab.{max w s}) JA JB).hom.app P).hom =
        eqToHom (congrArg (fun H : A ⥤ B => H.op ⋙ P.obj) e) := by
  subst G'
  ext V
  simp [Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]

/-- **The identity law of the transition of a system of abelian sheaves, in `eqToHom` form.**
The transition at an identity is the transport along the system's own equality of functors
`u_{𝟙 i} = 𝟭`, with no comparison isomorphism appearing.

This is the form a diagram of the system's sheaves pushed down to a fixed index wants for its
`map_id`: `abelianSheafPushforwardIdIso` is `Iso.refl`-bodied and so cannot be `dsimp`-unfolded
without making the goal ill-typed at implicit transparency, whereas this statement is already
`eqToHom` and composes with `eqToHom_trans`. -/
theorem transition_id_eqToHom
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    transition D F (𝟙 i) =
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (F.obj i).obj)
        (D.id_map i).symm) := by
  let := D.continuous (𝟙 i)
  rw [transition_id]
  show ((Functor.sheafPushforwardContinuousIso (eqToIso (D.id_map i))
    (Ab.{max u v w t}) (D.J i) (D.J i)).inv.app (F.obj i)).hom = _
  have h := pushforward_eqToIso_hom (JA := D.J i) (JB := D.J i)
    (G := 𝟭 (D.C i)) (G' := D.u (𝟙 i)) (D.id_map i).symm (F.obj i)
  exact h

/-- **The composition law of the transition of a system of abelian sheaves, in `eqToHom` form.**
The transition along a composite is the two transitions, whiskered, followed by the transport
along the system's own equality of functors `u_{a ≫ b} = u_b ⋙ u_a`, with no comparison
isomorphism appearing.

This is the `map_comp` companion of `transition_id_eqToHom`, and for the same reason: it is
already `eqToHom`, so it composes with `eqToHom_trans` instead of requiring
`abelianSheafPushforwardCompIso` to be unfolded. -/
theorem transition_comp_eqToHom
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i j k : D.I} (a : k ⟶ j) (b : j ⟶ i) :
    transition D F (a ≫ b) =
      (transition D F b ≫ Functor.whiskerLeft (D.u b).op (transition D F a)) ≫
        eqToHom (congrArg (fun H : D.C i ⥤ D.C k => H.op ⋙ (F.obj k).obj)
          (D.comp a b).symm) := by
  let := D.continuous a
  let := D.continuous b
  let := D.continuous (a ≫ b)
  let := Functor.isContinuous_comp (D.u b) (D.u a) (D.J i) (D.J j) (D.J k)
  rw [transition_comp]
  rw [Category.assoc]
  congr 1
  congr 1
  exact pushforward_eqToIso_hom (D.comp a b).symm (F.obj k)

section SystemCokernel

open InverseSystemOfFiniteSites


/-- Pushforward of abelian sheaves along a transition morphism of the system is additive. -/
local instance systemPushforward_additive (D : InverseSystemOfFiniteSites.{v, u, w})
    {i j : D.I} (a : i ⟶ j) :
    (abelianSheafPushforward.{v, u, w, t} D a).Additive where
  map_add := by intros; rfl

/-- **The transition of a system of abelian sheaves as a morphism of sheaves**, in adjoint
(direct-image) form: the adjunct of `F.map a : f_a⁻¹F_j ⟶ F_i` under
`abelianSheafAdjunction`. `transition` is its underlying map of presheaves.

This is the shape in which a diagram over `(Over i)ᵒᵖ` of sheaves pushed down to the level `i`
takes its arrows, the two coherence laws being `systemPushforwardMap_id` and
`systemPushforwardMap_comp`. -/
private def systemPushforwardMap (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) {i j : D.I} (a : i ⟶ j) :
    F.obj j ⟶ (abelianSheafPushforward.{v, u, w, t} D a).obj (F.obj i) :=
  (abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _ (F.map a)

/-- **The transition at an identity is the identity**, read through
`abelianSheafPushforwardIdIso`. This is the `map_id` law of a diagram of sheaves pushed down to a
fixed level; it is `transition_id` with the two sides read as morphisms of sheaves. -/
private theorem systemPushforwardMap_id (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    systemPushforwardMap D F (𝟙 i) =
      (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app (F.obj i) := by
  exact Sheaf.hom_ext (transition_id D F i)

/-- **The transition of a composite is the composite of the transitions**, read through
`abelianSheafPushforwardCompIso`. This is the `map_comp` law of a diagram of sheaves pushed down
to a fixed level; it is `transition_comp` with the three sides read as morphisms of sheaves. -/
private theorem systemPushforwardMap_comp (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) :
    systemPushforwardMap D F (a ≫ b) = systemPushforwardMap D F b ≫
      (abelianSheafPushforward.{v, u, w, t} D b).map (systemPushforwardMap D F a) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (F.obj i) := by
  exact Sheaf.hom_ext (transition_comp D F a b)

private theorem systemPushforwardMap_naturality (D : InverseSystemOfFiniteSites.{v, u, w})
    {F G : AbelianSheafSystem.{v, u, w, t} D} (f : AbelianSheafSystem.Hom F G)
    {i j : D.I} (a : i ⟶ j) :
    f.app j ≫ systemPushforwardMap D G a = systemPushforwardMap D F a ≫
      (abelianSheafPushforward.{v, u, w, t} D a).map (f.app i) := by
  unfold systemPushforwardMap
  rw [← Adjunction.homEquiv_naturality_left, f.naturality,
    Adjunction.homEquiv_naturality_right]

/-- **A system of abelian sheaves from transition maps written in the direct-image
direction.** A sheaf on each level together with maps `F_j ⟶ f_{a,*} F_i` that take the identity
transition to the canonical identification and a composite transition to the composite — the
adjoint form of the data of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem` — determines
such a system, the two cocycle conditions of the structure being the transposes of the two
hypotheses here.

This is the shape in which a system is produced in practice: the direct images are restriction
functors along the transition functors of the system of sites, so a comparison of successive
direct images with the direct image along a composite transition is available concretely,
whereas the inverse images are only characterised as left adjoints. -/
private def systemOfPushforwardMaps (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : ∀ i, Sheaf (D.J i) (Ab.{max u v w t}))
    (φ : ∀ {i j} (a : i ⟶ j), F j ⟶ (abelianSheafPushforward.{v, u, w, t} D a).obj (F i))
    (hid : ∀ i, φ (𝟙 i) = (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app (F i))
    (hcomp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k), φ (a ≫ b) = φ b ≫
      (abelianSheafPushforward.{v, u, w, t} D b).map (φ a) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (F i)) :
    AbelianSheafSystem.{v, u, w, t} D where
  obj := F
  map a := (abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _ |>.symm <| φ a
  map_id i := by
    have hh : (abelianSheafAdjunction.{v, u, w, t} D (𝟙 i)).homEquiv (F i) (F i)
        ((abelianSheafPullbackIdIso.{v, u, w, t} D i).hom.app (F i)) = φ (𝟙 i) := by
      rw [hid]
      exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
    rw [← hh]
    simpa only [Equiv.symm_apply_apply, Functor.id_obj] using
      (abelianSheafPullbackIdIso.{v, u, w, t} D i).inv_hom_id_app (F i)
  map_comp {i j k} a b := by
    apply (abelianSheafAdjunction.{v, u, w, t} D (a ≫ b)).homEquiv _ _ |>.injective
    dsimp only [abelianSheafPullbackCompIso]
    rw [homEquiv_leftAdjointUniq_inv_comp, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    change ((abelianSheafAdjunction.{v, u, w, t} D b).homEquiv _ _)
      (((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _)
        ((abelianSheafPullback.{v, u, w, t} D a).map
          (((abelianSheafAdjunction.{v, u, w, t} D b).homEquiv _ _).symm (φ b)) ≫
          ((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _).symm (φ a))) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (F i) = _
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact (hcomp a b).symm

private def systemCokernelMap (D : InverseSystemOfFiniteSites.{v, u, w})
    {F G : AbelianSheafSystem.{v, u, w, t} D} (f : AbelianSheafSystem.Hom F G)
    {i j : D.I} (a : i ⟶ j) :
    cokernel (f.app j) ⟶ (abelianSheafPushforward.{v, u, w, t} D a).obj (cokernel (f.app i)) :=
  cokernel.desc (f.app j)
    (systemPushforwardMap D G a ≫
      (abelianSheafPushforward.{v, u, w, t} D a).map (cokernel.π (f.app i))) (by
      rw [← Category.assoc, systemPushforwardMap_naturality, Category.assoc,
        ← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero])

private theorem systemCokernelMap_π (D : InverseSystemOfFiniteSites.{v, u, w})
    {F G : AbelianSheafSystem.{v, u, w, t} D} (f : AbelianSheafSystem.Hom F G)
    {i j : D.I} (a : i ⟶ j) :
    cokernel.π (f.app j) ≫ systemCokernelMap D f a =
      systemPushforwardMap D G a ≫
        (abelianSheafPushforward.{v, u, w, t} D a).map (cokernel.π (f.app i)) :=
  cokernel.π_desc _ _ _

private def systemCokernel (D : InverseSystemOfFiniteSites.{v, u, w})
    {F G : AbelianSheafSystem.{v, u, w, t} D} (f : AbelianSheafSystem.Hom F G) :
    AbelianSheafSystem.{v, u, w, t} D :=
  systemOfPushforwardMaps D (fun i => cokernel (f.app i)) (systemCokernelMap D f)
    (fun i => by
      apply (cancel_epi (cokernel.π (f.app i))).mp
      rw [systemCokernelMap_π, systemPushforwardMap_id]
      exact ((abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.naturality
        (cokernel.π (f.app i))).symm)
    (fun {i j k} a b => by
      apply (cancel_epi (cokernel.π (f.app k))).mp
      rw [systemCokernelMap_π, systemPushforwardMap_comp]
      simp only [Category.assoc]
      rw [← NatTrans.naturality, reassoc_of% (systemCokernelMap_π D f b)]
      simp only [Functor.comp_map]
      simpa only [Functor.map_comp, Category.assoc] using congrArg
        (fun h => systemPushforwardMap D G b ≫
          (abelianSheafPushforward.{v, u, w, t} D b).map h ≫
          (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (cokernel (f.app i)))
        (systemCokernelMap_π D f a).symm)

attribute [local instance_reducible] systemOfPushforwardMaps systemCokernel

private def systemHomComp {D : InverseSystemOfFiniteSites.{v, u, w}}
    {F G H : AbelianSheafSystem.{v, u, w, t} D}
    (f : AbelianSheafSystem.Hom F G) (g : AbelianSheafSystem.Hom G H) :
    AbelianSheafSystem.Hom F H where
  app i := f.app i ≫ g.app i
  naturality a := by
    rw [Functor.map_comp, Category.assoc, g.naturality, ← Category.assoc, f.naturality]
    simp only [Category.assoc]

private def systemCokernelπ (D : InverseSystemOfFiniteSites.{v, u, w})
    {F G : AbelianSheafSystem.{v, u, w, t} D} (f : AbelianSheafSystem.Hom F G) :
    AbelianSheafSystem.Hom G (systemCokernel D f) where
  app i := cokernel.π (f.app i)
  naturality a := by
    apply (abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _ |>.injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    change cokernel.π (f.app _) ≫
      ((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _)
        (((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _).symm
          (systemCokernelMap D f a)) = _
    rw [Equiv.apply_symm_apply]
    exact systemCokernelMap_π D f a

private def injectiveSystem (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) : AbelianSheafSystem.{v, u, w, t} D :=
  (AbelianSheafSystem.exists_mono_to_pointwise_injective F).choose

private def injectiveSystemι (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) :
    AbelianSheafSystem.Hom F (injectiveSystem D F) :=
  (AbelianSheafSystem.exists_mono_to_pointwise_injective F).choose_spec.choose

private theorem injectiveSystemι_mono (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    Mono ((injectiveSystemι D F).app i) :=
  (AbelianSheafSystem.exists_mono_to_pointwise_injective F).choose_spec.choose_spec.1 i

private theorem injectiveSystem_injective (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    Injective ((injectiveSystem D F).obj i) :=
  (AbelianSheafSystem.exists_mono_to_pointwise_injective F).choose_spec.choose_spec.2 i

private def systemSyzygy (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) : ℕ → AbelianSheafSystem.{v, u, w, t} D
  | 0 => F
  | n + 1 => systemCokernel D (injectiveSystemι D (systemSyzygy D F n))

attribute [local instance_reducible] systemSyzygy

private def systemResolutionDifferential (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (n : ℕ) :
    AbelianSheafSystem.Hom (injectiveSystem D (systemSyzygy D F n))
      (injectiveSystem D (systemSyzygy D F (n + 1))) :=
  systemHomComp (systemCokernelπ D (injectiveSystemι D (systemSyzygy D F n)))
    (injectiveSystemι D (systemSyzygy D F (n + 1)))

private theorem systemResolutionDifferential_comp (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (n : ℕ) (i : D.I) :
    (systemResolutionDifferential D F n).app i ≫
      (systemResolutionDifferential D F (n + 1)).app i = 0 := by
  dsimp only [systemResolutionDifferential, systemHomComp, systemCokernelπ,
    systemSyzygy, systemCokernel, systemOfPushforwardMaps]
  simp only [Category.assoc, cokernel.condition_assoc, zero_comp, comp_zero]

private def systemResolutionComplex (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    CochainComplex (Sheaf (D.J i) (Ab.{max u v w t})) ℕ :=
  CochainComplex.of (fun n => (injectiveSystem D (systemSyzygy D F n)).obj i)
    (fun n => (systemResolutionDifferential D F n).app i)
    (fun n => systemResolutionDifferential_comp D F n i)

private theorem exact_comp_epi_mono
    {A : Type*} [Category* A] [Abelian A] {V W X Y Z : A}
    (e : V ⟶ W) (f : W ⟶ X) (g : X ⟶ Y) (m : Y ⟶ Z)
    [Epi e] [Mono m] (hfg : f ≫ g = 0) (h : (ShortComplex.mk f g hfg).Exact) :
    (ShortComplex.mk (e ≫ f) (g ≫ m) (by
      simp only [Category.assoc, hfg, reassoc_of% hfg, zero_comp, comp_zero])).Exact := by
  let S := ShortComplex.mk (e ≫ f) g (by
    simp only [Category.assoc, hfg, comp_zero])
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (show S ⟶ ShortComplex.mk f g hfg from
      { τ₁ := e, τ₂ := 𝟙 _, τ₃ := 𝟙 _ })).2 h
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (show S ⟶ ShortComplex.mk (e ≫ f) (g ≫ m) _ from
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := m })).1 hS

private theorem systemResolutionComplex_exactAt_succ (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) (n : ℕ) :
    (systemResolutionComplex D F i).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    systemResolutionComplex]
  simp only [CochainComplex.of_d]
  let := injectiveSystemι_mono D (systemSyzygy D F (n + 1 + 1)) i
  exact exact_comp_epi_mono
    (cokernel.π ((injectiveSystemι D (systemSyzygy D F n)).app i))
    ((injectiveSystemι D (systemSyzygy D F (n + 1))).app i)
    (cokernel.π ((injectiveSystemι D (systemSyzygy D F (n + 1))).app i))
    ((injectiveSystemι D (systemSyzygy D F (n + 1 + 1))).app i)
    (cokernel.condition _) (ShortComplex.cokernelSequence_exact _)

private def systemResolutionι (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    (CochainComplex.single₀ _).obj (F.obj i) ⟶ systemResolutionComplex D F i :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(injectiveSystemι D F).app i, by
      simp only [systemResolutionComplex, systemSyzygy]
      change (injectiveSystemι D F).app i ≫
        cokernel.π ((injectiveSystemι D F).app i) ≫ _ = _
      rw [cokernel.condition_assoc, zero_comp]
      exact rfl⟩

private theorem systemResolutionι_quasiIso (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    QuasiIso (systemResolutionι D F i) := ⟨fun n => by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · let := injectiveSystemι_mono D F i
      let := injectiveSystemι_mono D (systemSyzygy D F 1) i
      have hex := exact_comp_epi_mono (𝟙 _)
        ((injectiveSystemι D F).app i) (cokernel.π ((injectiveSystemι D F).app i))
        ((injectiveSystemι D (systemSyzygy D F 1)).app i)
        (cokernel.condition _) (ShortComplex.cokernelSequence_exact _)
      refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨hex, by dsimp; infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact systemResolutionComplex_exactAt_succ D F i n
    · exact CochainComplex.exactAt_succ_single_obj _ _⟩

private def systemInjectiveResolution (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) : InjectiveResolution (F.obj i) where
  cocomplex := systemResolutionComplex D F i
  injective n := injectiveSystem_injective D (systemSyzygy D F n) i
  ι := systemResolutionι D F i
  quasiIso := systemResolutionι_quasiIso D F i

end SystemCokernel

attribute [local instance_reducible] systemOfPushforwardMaps systemCokernel systemSyzygy

private theorem exists_isCohomologyMap_transition
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {j k : D.I} (a : k ⟶ j)
    (hG : (D.u a).IsContinuous (D.J j) (D.J k))
    (hL : ((D.u a).sheafPullback (Ab.{max u v w t}) (D.J j) (D.J k)).PreservesMonomorphisms)
    (V : D.C j) (p : ℕ) :
    ∃ m, IsCohomologyMap (D.J j) (D.J k) (D.u a)
      (transition.{v, u, w, t} D F a) V p m := by
  let : (D.u a).IsContinuous (D.J j) (D.J k) := hG
  let φ := ((InverseSystemOfFiniteSites.abelianSheafAdjunction.{v, u, w, t} D a).homEquiv
    (F.obj j) (F.obj k)) (F.map a)
  obtain ⟨m, hm⟩ := exists_isCohomologyMap_of_sheafHom
    (D.J j) (D.J k) (D.u a) hG hL φ V p
  exact ⟨m, by simpa [transition, φ] using hm⟩

private noncomputable def transitionCochainLift
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i : D.I} {A B : Over i} (f : A ⟶ B)
    (hG : (D.u f.left).IsContinuous (D.J B.left) (D.J A.left))
    (hL : ((D.u f.left).sheafPullback (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).PreservesMonomorphisms)
    (I : InjectiveResolution (F.obj B.left)) (J : InjectiveResolution (F.obj A.left)) :
    I.cocomplex ⟶
      (((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
        (D.J B.left) (D.J A.left)).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex := by
  letI : (D.u f.left).IsContinuous (D.J B.left) (D.J A.left) := hG
  letI : ((D.u f.left).sheafPullback (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).PreservesMonomorphisms := hL
  let adj := (D.u f.left).sheafAdjunctionContinuous (Ab.{max u v w t})
    (D.J B.left) (D.J A.left)
  haveI : ((D.u f.left).sheafPullback (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).PreservesMonomorphisms := hL
  haveI : ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let φ : F.obj B.left ⟶
      ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
        (D.J B.left) (D.J A.left)).obj (F.obj A.left) :=
    ⟨transition.{v, u, w, t} D F f.left⟩
  let T := (((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  have hT : ∀ n, Injective (T.X n) := by
    intro n
    exact (D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left) |>.injective_obj_of_injective (J.injective n)
  have hsingle : F.obj A.left =
      ((CochainComplex.single₀ (Sheaf (D.J A.left) (Ab.{max u v w t}))).obj
        (F.obj A.left)).X 0 := rfl
  let f₀ : F.obj B.left ⟶ T.X 0 :=
    φ ≫ ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).map (eqToHom hsingle ≫ J.ι.f 0)
  have hι : J.ι.f 0 ≫ J.cocomplex.d 0 1 = 0 := J.ι_f_zero_comp_complex_d
  have hηd : (eqToHom hsingle ≫ J.ι.f 0) ≫ J.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc, hι, comp_zero]
  have hf : f₀ ≫ T.d 0 1 = 0 := by
    change φ ≫ ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).map (eqToHom hsingle ≫ J.ι.f 0) ≫
        ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
          (D.J B.left) (D.J A.left)).map (J.cocomplex.d 0 1) = 0
    rw [← Functor.map_comp, hηd, Functor.map_zero, comp_zero]
  exact liftCochainMap I hT f₀ hf

private theorem transitionCochainLift_comm
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i : D.I} {A B : Over i} (f : A ⟶ B)
    (hG : (D.u f.left).IsContinuous (D.J B.left) (D.J A.left))
    (hL : ((D.u f.left).sheafPullback (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).PreservesMonomorphisms)
    (I : InjectiveResolution (F.obj B.left)) (J : InjectiveResolution (F.obj A.left)) :
    (I.ι.f 0).hom ≫ ((transitionCochainLift D F f hG hL I J).f 0).hom =
      (transition.{v, u, w, t} D F f.left) ≫
        Functor.whiskerLeft (D.u f.left).op (J.ι.f 0).hom := by
  let : (D.u f.left).IsContinuous (D.J B.left) (D.J A.left) := hG
  let : ((D.u f.left).sheafPullback (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).PreservesMonomorphisms := hL
  let φ : F.obj B.left ⟶
      ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
        (D.J B.left) (D.J A.left)).obj (F.obj A.left) :=
    ⟨transition.{v, u, w, t} D F f.left⟩
  let T := (((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  have hT : ∀ n, Injective (T.X n) := by
    intro n
    let adj := (D.u f.left).sheafAdjunctionContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)
    have : ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
        (D.J B.left) (D.J A.left)).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
    exact (D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left) |>.injective_obj_of_injective (J.injective n)
  have hsingle : F.obj A.left =
      ((CochainComplex.single₀ (Sheaf (D.J A.left) (Ab.{max u v w t}))).obj
        (F.obj A.left)).X 0 := rfl
  let f₀ : F.obj B.left ⟶ T.X 0 :=
    φ ≫ ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).map (eqToHom hsingle ≫ J.ι.f 0)
  have hι : J.ι.f 0 ≫ J.cocomplex.d 0 1 = 0 := J.ι_f_zero_comp_complex_d
  have hηd : (eqToHom hsingle ≫ J.ι.f 0) ≫ J.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc, hι, comp_zero]
  have hf : f₀ ≫ T.d 0 1 = 0 := by
    show φ ≫ ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).map (eqToHom hsingle ≫ J.ι.f 0) ≫
        ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
          (D.J B.left) (D.J A.left)).map (J.cocomplex.d 0 1) = 0
    rw [← Functor.map_comp, hηd, Functor.map_zero, comp_zero]
  have hLift : (I.ι.f 0).hom ≫
      ((transitionCochainLift D F f hG hL I J).f 0).hom = f₀.hom := by
    show (I.ι.f 0 ≫ (liftCochainMap I hT f₀ hf).f 0).hom = f₀.hom
    exact congrArg (fun g => g.hom) (liftCochainMap_comm I hT f₀ hf)
  have hF : f₀.hom = transition.{v, u, w, t} D F f.left ≫
      Functor.whiskerLeft (D.u f.left).op (J.ι.f 0).hom := by
    cases hsingle
    ext U
    rfl
  exact hLift.trans hF

private noncomputable def transitionCohomologyMap
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i : D.I} {A B : Over i} (f : A ⟶ B)
    (hG : (D.u f.left).IsContinuous (D.J B.left) (D.J A.left))
    (hL : ((D.u f.left).sheafPullback (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).PreservesMonomorphisms)
    (I : InjectiveResolution (F.obj B.left)) (J : InjectiveResolution (F.obj A.left))
    (V : D.C B.left) (p : ℕ) :
    ((((sheafSections (D.J B.left) (Ab.{max u v w t})).obj (op V)).rightDerived p).obj
      (F.obj B.left)) ⟶
      ((((sheafSections (D.J A.left) (Ab.{max u v w t})).obj
        (op ((D.u f.left).obj V))).rightDerived p).obj (F.obj A.left)) := by
  letI : (D.u f.left).IsContinuous (D.J B.left) (D.J A.left) := hG
  exact cohomologyMapOfLift (D.u f.left) I J
    (transitionCochainLift D F f hG hL I J) V p

private theorem isCohomologyMap_transitionCohomologyMap
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i : D.I} {A B : Over i} (f : A ⟶ B)
    (hG : (D.u f.left).IsContinuous (D.J B.left) (D.J A.left))
    (hL : ((D.u f.left).sheafPullback (Ab.{max u v w t})
      (D.J B.left) (D.J A.left)).PreservesMonomorphisms)
    (I : InjectiveResolution (F.obj B.left)) (J : InjectiveResolution (F.obj A.left))
    (V : D.C B.left) (p : ℕ) :
    IsCohomologyMap (D.J B.left) (D.J A.left) (D.u f.left)
      (transition.{v, u, w, t} D F f.left) V p
      (transitionCohomologyMap D F f hG hL I J V p) := by
  let : (D.u f.left).IsContinuous (D.J B.left) (D.J A.left) := hG
  let lift := transitionCochainLift D F f hG hL I J
  let φ : F.obj B.left ⟶
      ((D.u f.left).sheafPushforwardContinuous (Ab.{max u v w t})
        (D.J B.left) (D.J A.left)).obj (F.obj A.left) :=
    ⟨transition.{v, u, w, t} D F f.left⟩
  have h0 := transitionCochainLift_comm D F f hG hL I J
  have h0' : (I.ι.f 0).hom ≫ (lift.f 0).hom =
      φ.hom ≫ Functor.whiskerLeft (D.u f.left).op (J.ι.f 0).hom := by
    show (I.ι.f 0).hom ≫
      ((transitionCochainLift D F f hG hL I J).f 0).hom =
        (transition.{v, u, w, t} D F f.left) ≫
          Functor.whiskerLeft (D.u f.left).op (J.ι.f 0).hom
    exact h0
  exact isCohomologyMap_cohomologyMapOfLift (D.u f.left) φ I J lift h0' V p


/-- Restriction along `u_k` of a presheaf on the colimit site, read through `u_a`, is restriction
along `u_j`: the functor identity `u_a ⋙ u_k = u_j` of a colimit of sites. -/
theorem restrict_eq (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    {j k : D.I} (a : k ⟶ j) (H : Cᵒᵖ ⥤ Ab.{max u v w t}) :
    (D.u a).op ⋙ ((uC k).op ⋙ H) = (uC j).op ⋙ H := by
  have hop : (D.u a ⋙ uC k).op = (D.u a).op ⋙ (uC k).op := rfl
  rw [← Functor.assoc, ← hop, hu a]

/-- A family of maps `F_j ⟶ u_j^{-1}H` of presheaves of abelian groups is compatible with the
transitions of the system. -/
def IsCompatible (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (H : Cᵒᵖ ⥤ Ab.{max u v w t})
    (g : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ H) : Prop :=
  ∀ {j k : D.I} (a : k ⟶ j),
    g j = transition.{v, u, w, t} D F a ≫ Functor.whiskerLeft (D.u a).op (g k) ≫
      eqToHom (restrict_eq.{v, u, w, t} D uC hu a H)

/-- `IsColimitPresentation` says that the abelian sheaf `𝒢` on the colimit site, with the
compatible family `ι`, is `colim fᵢ⁻¹Fᵢ`: every compatible family of maps to an abelian sheaf
`H` on the colimit site factors uniquely through `ι`. This is the universal property by which
the case `p = 0` of the source, Tag 09YN, presents the same colimit for sheaves of sets. -/
def IsColimitPresentation (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj) : Prop :=
  IsCompatible.{v, u, w, t} D uC hu F 𝒢.obj ι ∧
    ∀ (H : Sheaf K.toGrothendieck (Ab.{max u v w t}))
      (g : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ H.obj),
      IsCompatible.{v, u, w, t} D uC hu F H.obj g →
        ∃! h : 𝒢 ⟶ H, ∀ j, ι j ≫ Functor.whiskerLeft (uC j).op h.hom = g j

/-! ### The cohomology diagram over the arrows into a fixed index -/

/-- For `f : A ⟶ B` in `Over i`, the object `u_{A.hom}(X)` is `u_{f.left}(u_{B.hom}(X))`. -/
theorem uObj_eq (D : InverseSystemOfFiniteSites.{v, u, w}) {i : D.I} {A B : Over i} (f : A ⟶ B)
    (X : D.C i) : (D.u A.hom).obj X = (D.u f.left).obj ((D.u B.hom).obj X) := by
  rw [← Over.w f]
  exact Functor.congr_obj (D.comp f.left B.hom) X

/-- For `A : Over i`, the object `u_i(X)` of the colimit site is `u_{A.left}(u_{A.hom}(X))`. -/
theorem uLeg_eq (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    {i : D.I} (A : Over i) (X : D.C i) :
    (uC i).obj X = (uC A.left).obj ((D.u A.hom).obj X) :=
  (Functor.congr_obj (hu A.hom) X).symm

/-- A presentation of the canonical cohomology diagram over the arrows `a : j ⟶ i` and of its
canonical cocone at the cohomology of the colimit sheaf. Every value of the diagram is identified
with the cohomology `Hᵖ(u_a(X), F_j)`, and every arrow of the diagram and every leg of the cocone
is required to be the canonical cohomology map. -/
structure CohomologyCocone (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj) (i : D.I) (X : D.C i) (p : ℕ) where
  /-- The diagram of cohomology groups, indexed by the arrows `a : j ⟶ i`. -/
  diagram : (Over i)ᵒᵖ ⥤ Ab.{max u v w t}
  /-- The value at `a : j ⟶ i` is the cohomology of `F j` over `u_a(X)`. -/
  objIso : ∀ A : Over i, diagram.obj (op A) ≅
    ((((sheafSections (D.J A.left) (Ab.{max u v w t})).obj
      (op ((D.u A.hom).obj X))).rightDerived p).obj (F.obj A.left))
  /-- Every arrow of the diagram is the canonical cohomology map of the transition. -/
  map_eq : ∀ {A B : Over i} (f : A ⟶ B),
    IsCohomologyMap (D.J B.left) (D.J A.left) (D.u f.left)
      (transition.{v, u, w, t} D F f.left) ((D.u B.hom).obj X) p
      ((objIso B).inv ≫ diagram.map f.op ≫ (objIso A).hom ≫
        cohomologyCongr (D.J A.left) p (uObj_eq.{v, u, w} D f X) (F.obj A.left))
  /-- The cocone at the cohomology of the colimit sheaf over `u_i(X)`. -/
  leg : diagram ⟶ (Functor.const (Over i)ᵒᵖ).obj
    ((((sheafSections K.toGrothendieck (Ab.{max u v w t})).obj
      (op ((uC i).obj X))).rightDerived p).obj 𝒢)
  /-- Every leg of the cocone is the canonical cohomology map of the structure map of the
  colimit. -/
  leg_eq : ∀ A : Over i,
    IsCohomologyMap (D.J A.left) K.toGrothendieck (uC A.left) (ι A.left)
      ((D.u A.hom).obj X) p
      ((objIso A).inv ≫ leg.app (op A) ≫
        cohomologyCongr K.toGrothendieck p (uLeg_eq.{v, u, w} D uC hu A X) 𝒢)

/-- The cocone of the cohomology diagram, with vertex the cohomology of the colimit sheaf. -/
@[simps]
def CohomologyCocone.cocone {D : InverseSystemOfFiniteSites.{v, u, w}} {C : Type w}
    [SmallCategory C]
    {uC : ∀ i, D.C i ⥤ C} {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
    {K : Precoverage C} {F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    {𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t})}
    {ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj} {i : D.I} {X : D.C i} {p : ℕ}
    (E : CohomologyCocone.{v, u, w, t} D uC hu K F 𝒢 ι i X p) : Cocone E.diagram :=
  ⟨_, E.leg⟩

private theorem cohomologyCongr_isIso
    {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A) (p : ℕ)
    {V V' : A} (h : V = V') (P : Sheaf JA (Ab.{max w s})) :
    IsIso (cohomologyCongr JA p h P) := by
  unfold cohomologyCongr
  infer_instance

private def cohomologyDiagramIso
    {D : InverseSystemOfFiniteSites.{v, u, w}} {C : Type w} [SmallCategory C]
    {uC : ∀ i, D.C i ⥤ C}
    {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
    {K : Precoverage C} {F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    {𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t})}
    {ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj} {i : D.I} {X : D.C i} {p : ℕ}
    (htrans : ∀ {j k : D.I} (a : j ⟶ k),
      (InverseSystemOfFiniteSites.abelianSheafPushforward.{v, u, w, t}
        D a).PreservesInjectiveObjects)
    (E E' : CohomologyCocone.{v, u, w, t} D uC hu K F 𝒢 ι i X p) :
    E.diagram ≅ E'.diagram := by
  refine NatIso.ofComponents (fun A => E.objIso A.unop ≪≫ (E'.objIso A.unop).symm) ?_
  intro A B f
  let := D.continuous f.unop.left
  let : ((D.u f.unop.left).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J A.unop.left) (D.J B.unop.left)).PreservesInjectiveObjects := htrans f.unop.left
  have hm := isCohomologyMap_unique (D.u f.unop.left)
    (transition D F f.unop.left) ((D.u A.unop.hom).obj X) p
    (E.map_eq f.unop) (E'.map_eq f.unop)
  let := cohomologyCongr_isIso (D.J B.unop.left) p (uObj_eq D f.unop X) (F.obj B.unop.left)
  have h : (E.objIso A.unop).inv ≫ E.diagram.map f ≫ (E.objIso B.unop).hom =
      (E'.objIso A.unop).inv ≫ E'.diagram.map f ≫ (E'.objIso B.unop).hom := by
    apply (cancel_mono
      (cohomologyCongr (D.J B.unop.left) p (uObj_eq D f.unop X) (F.obj B.unop.left))).mp
    simpa only [Quiver.Hom.op_unop, Category.assoc] using hm
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  apply (cancel_epi (E.objIso A.unop).inv).mp
  apply (cancel_mono (E'.objIso B.unop).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    using h

section AbelianRestriction

/-- Restriction along a morphism of sites preserves injective abelian sheaves, with coefficients
in any universe containing the universe of the sites. The inverse image is exact there
(Stacks 04JC) and restriction is its right adjoint, which is Stacks 0730. -/
private theorem restriction_preservesInjectiveObjects
    {C D : Type w} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (a : C ⥤ D) (ha : a.IsMorphismOfSites J K) :
    letI := ha.isContinuous
    (a.sheafPushforwardContinuous (Ab.{max w s}) J K).PreservesInjectiveObjects := by
  let := ha.isContinuous
  have : PreservesFilteredColimitsOfSize.{w, w} (forget (Ab.{max w s})) :=
    preservesFilteredColimitsOfSize_shrink _
  have : HasSheafify J (Ab.{max w s}) := inferInstance
  have :=
    Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_ab_largeSections.{s, w} ha
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (a.sheafAdjunctionContinuous (Ab.{max w s}) J K)

end AbelianRestriction

section SectionsDiagram

private def sectionsMapTo {A B : Type w} [SmallCategory A] [SmallCategory B]
    (G : A ⥤ B) {P : Aᵒᵖ ⥤ Ab.{max w s}} {Q : Bᵒᵖ ⥤ Ab.{max w s}}
    (φ : P ⟶ G.op ⋙ Q) (V : A) (W : B) (h : G.obj V = W) :
    P.obj (op V) ⟶ Q.obj (op W) :=
  φ.app (op V) ≫ Q.map (eqToHom (congrArg op h))

private theorem sectionsMapTo_congr {A B : Type w} [SmallCategory A] [SmallCategory B]
    {G G' : A ⥤ B} {P : Aᵒᵖ ⥤ Ab.{max w s}} {Q : Bᵒᵖ ⥤ Ab.{max w s}}
    (φ : P ⟶ G.op ⋙ Q) (φ' : P ⟶ G'.op ⋙ Q) (V : A) (W : B)
    (h : G = G')
    (hφ : φ ≫ eqToHom (congrArg (fun T : A ⥤ B => T.op ⋙ Q) h) = φ')
    {e : G.obj V = W} {e' : G'.obj V = W} :
    sectionsMapTo G φ V W e = sectionsMapTo G' φ' V W e' := by
  subst G'
  simp only [eqToHom_refl, Category.comp_id] at hφ
  subst φ'
  rfl

private theorem sectionsMapTo_comp {A B C : Type w}
    [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (G : A ⥤ B) (H : B ⥤ C)
    {P : Aᵒᵖ ⥤ Ab.{max w s}} {Q : Bᵒᵖ ⥤ Ab.{max w s}} {R : Cᵒᵖ ⥤ Ab.{max w s}}
    (φ : P ⟶ G.op ⋙ Q) (ψ : Q ⟶ H.op ⋙ R)
    (U : A) (V : B) (W : C) (h : G.obj U = V) (h' : H.obj V = W) :
    sectionsMapTo G φ U V h ≫ sectionsMapTo H ψ V W h' =
      sectionsMapTo (G ⋙ H) (φ ≫ Functor.whiskerLeft G.op ψ) U W
        ((congrArg H.obj h).trans h') := by
  subst V
  subst W
  simp [sectionsMapTo]

private theorem sectionsMapTo_naturality {A B : Type w}
    [SmallCategory A] [SmallCategory B] (G : A ⥤ B)
    {P P' : Aᵒᵖ ⥤ Ab.{max w s}} {Q Q' : Bᵒᵖ ⥤ Ab.{max w s}}
    (φ : P ⟶ G.op ⋙ Q) (φ' : P' ⟶ G.op ⋙ Q') (f : P ⟶ P') (g : Q ⟶ Q')
    (hfg : f ≫ φ' = φ ≫ Functor.whiskerLeft G.op g)
    (V : A) (W : B) (h : G.obj V = W) :
    f.app (op V) ≫ sectionsMapTo G φ' V W h =
      sectionsMapTo G φ V W h ≫ g.app (op W) := by
  subst W
  simpa [sectionsMapTo] using congrArg (fun t => t.app (op V)) hfg

private theorem cohomologyMapTo_zero_comm {A B : Type w}
    [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
    (G : A ⥤ B) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (V : A) (W : B) (h : G.obj V = W) :
    ((sheafSections JA (Ab.{max w s})).obj (op V)).toRightDerivedZero.app P ≫
      cohomologyMapTo G φ V W h 0 =
      sectionsMapTo G φ V W h ≫
        ((sheafSections JB (Ab.{max w s})).obj (op W)).toRightDerivedZero.app Q := by
  subst W
  simpa [cohomologyMapTo, cohomologyCongr, sectionsMapTo] using
    isCohomologyMap_zero_comm G φ V (isCohomologyMap_canonical G φ V 0)

private def sectionsDiagram (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) (X : D.C i) :
    (Over i)ᵒᵖ ⥤ Ab.{max u v w t} where
  obj A := (F.obj A.unop.left).obj.obj (op ((D.u A.unop.hom).obj X))
  map f := sectionsMapTo (D.u f.unop.left) (transition D F f.unop.left)
    ((D.u _).obj X) ((D.u _).obj X) (uObj_eq D f.unop X).symm
  map_id A := by
    change sectionsMapTo (D.u (𝟙 A.unop.left)) (transition D F (𝟙 A.unop.left)) _ _ _ = _
    calc
      _ = sectionsMapTo (𝟭 _) (𝟙 (F.obj A.unop.left).obj)
          ((D.u A.unop.hom).obj X) ((D.u A.unop.hom).obj X) rfl := by
        apply sectionsMapTo_congr _ _ _ _ (D.id_map A.unop.left)
        rw [transition_id_eqToHom, eqToHom_trans]
        rfl
      _ = 𝟙 _ := by simp [sectionsMapTo]
  map_comp f g := by
    rw [sectionsMapTo_comp]
    symm
    exact sectionsMapTo_congr _ _ _ _ (D.comp g.unop.left f.unop.left).symm
      (transition_comp_eqToHom D F g.unop.left f.unop.left).symm

private def sectionsDiagramMap {D : InverseSystemOfFiniteSites.{v, u, w}}
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) (i : D.I) (X : D.C i) :
    sectionsDiagram D F i X ⟶ sectionsDiagram D G i X where
  app A := (f.app A.unop.left).hom.app (op ((D.u A.unop.hom).obj X))
  naturality A B a := by
    symm
    exact sectionsMapTo_naturality (D.u a.unop.left)
      (transition D F a.unop.left) (transition D G a.unop.left)
      (f.app A.unop.left).hom (f.app B.unop.left).hom
      (congrArg (fun t => t.hom) (systemPushforwardMap_naturality D f a.unop.left))
      _ _ (uObj_eq D a.unop X).symm

private def sectionsCocone (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t}) (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G)
    (hι : IsCompatible D uC hu F G ι) (i : D.I) (X : D.C i) :
    Cocone (sectionsDiagram D F i X) where
  pt := G.obj (op ((uC i).obj X))
  ι := {
    app A := sectionsMapTo (uC A.unop.left) (ι A.unop.left)
      ((D.u A.unop.hom).obj X) ((uC i).obj X) (uLeg_eq D uC hu A.unop X).symm
    naturality A B f := by
      change sectionsMapTo (D.u f.unop.left) (transition D F f.unop.left)
        ((D.u A.unop.hom).obj X) ((D.u B.unop.hom).obj X) (uObj_eq D f.unop X).symm ≫
        sectionsMapTo _ _ _ _ _ = _ ≫ 𝟙 _
      rw [Category.comp_id, sectionsMapTo_comp]
      exact sectionsMapTo_congr _ _ _ _ (hu f.unop.left) (hι f.unop.left).symm }

end SectionsDiagram

section TotalSite



@[implicit_reducible] private def oppositeSiteDiagram
    (D : InverseSystemOfFiniteSites.{v, u, w}) : D.Iᵒᵖ ⥤ Cat.{w, w} where
  obj i := Cat.of (D.C i.unop)ᵒᵖ
  map a := (D.u a.unop).op.toCatHom
  map_id i := by
    apply Cat.Hom.ext
    change (D.u (𝟙 i.unop)).op = 𝟭 (D.C i.unop)ᵒᵖ
    rw [D.id_map]
    rfl
  map_comp a b := by
    apply Cat.Hom.ext
    change (D.u (b.unop ≫ a.unop)).op = (D.u a.unop).op ⋙ (D.u b.unop).op
    rw [D.comp]
    rfl

/-- `map_id` for `systemPresheafOnTotal`: at an identity index map, the transition and the
induced map on fibres are mutually inverse `eqToHom`s. -/
private theorem systemPresheafOnTotal_map_id (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (X : Grothendieck (oppositeSiteDiagram D)) :
    (transition D F (Grothendieck.Hom.base (𝟙 X)).unop).app X.fiber ≫
        (F.obj X.base.unop).obj.map (Grothendieck.Hom.fiber (𝟙 X)) =
      𝟙 ((F.obj X.base.unop).obj.obj X.fiber) := by
  have h : (D.u (𝟙 X.base.unop)).op = 𝟭 (D.C X.base.unop)ᵒᵖ := by
    rw [D.id_map]; rfl
  simp only [Grothendieck.id_base, Grothendieck.id_fiber, unop_id, transition_id_eqToHom,
    eqToHom_app, eqToHom_map (F.obj X.base.unop).obj (Functor.congr_obj h X.fiber),
    eqToHom_trans, eqToHom_refl]

/-- `map_comp` for `systemPresheafOnTotal`: the transition at a composite index map agrees with
the composite of the transitions, up to the `eqToHom` built into `Grothendieck.comp`. -/
private theorem systemPresheafOnTotal_map_comp (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {X Y Z : Grothendieck (oppositeSiteDiagram D)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transition D F (f ≫ g).base.unop).app X.fiber ≫
        (F.obj Z.base.unop).obj.map (f ≫ g).fiber =
      ((transition D F f.base.unop).app X.fiber ≫
          (F.obj Y.base.unop).obj.map f.fiber) ≫
        (transition D F g.base.unop).app Y.fiber ≫
          (F.obj Z.base.unop).obj.map g.fiber := by
  have h : (D.u (g.base.unop ≫ f.base.unop)).op =
      (D.u f.base.unop).op ⋙ (D.u g.base.unop).op := by
    rw [D.comp]; rfl
  simp [Grothendieck.comp_fiber, transition_comp_eqToHom, eqToHom_app, Functor.map_comp,
    eqToHom_map (F.obj Z.base.unop).obj (Functor.congr_obj h X.fiber),
    oppositeSiteDiagram, Category.assoc]

private def systemPresheafOnTotal (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) :
    Grothendieck (oppositeSiteDiagram D) ⥤ Ab.{max u v w t} where
  obj X := (F.obj X.base.unop).obj.obj X.fiber
  map {X Y} f := (transition D F f.base.unop).app X.fiber ≫
    (F.obj Y.base.unop).obj.map f.fiber
  map_id X := systemPresheafOnTotal_map_id D F X
  map_comp f g := systemPresheafOnTotal_map_comp D F f g

private theorem whiskerLeft_eqToHom'
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B) {G H : B ⥤ C} (h : G = H) :
    Functor.whiskerLeft F (eqToHom h) = eqToHom (congrArg (Functor.comp F) h) := by
  subst H
  rfl

private def totalToColimit (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j) :
    Grothendieck (oppositeSiteDiagram D) ⥤ Cᵒᵖ where
  obj X := (uC X.base.unop).op.obj X.fiber
  map {X Y} f :=
    (eqToHom (congrArg Functor.op (hu f.base.unop)).symm).app X.fiber ≫
      (uC Y.base.unop).op.map f.fiber
  map_id X := by
    change (eqToHom (congrArg Functor.op (hu (𝟙 X.base.unop))).symm).app X.fiber ≫
      (uC X.base.unop).op.map (eqToHom
        (congrArg op (Functor.congr_obj (D.id_map X.base.unop) X.fiber.unop))) = _
    rw [eqToHom_app, eqToHom_map]
    simp
  map_comp {X Y Z} f g := by
    have h : (D.u (g.base.unop ≫ f.base.unop)).op =
        (D.u f.base.unop).op ⋙ (D.u g.base.unop).op := by
      rw [D.comp]; rfl
    change (eqToHom (congrArg Functor.op (hu (g.base.unop ≫ f.base.unop))).symm).app X.fiber ≫
        (uC Z.base.unop).op.map (eqToHom (Functor.congr_obj h X.fiber) ≫
          (D.u g.base.unop).op.map f.fiber ≫ g.fiber) =
      ((eqToHom (congrArg Functor.op (hu f.base.unop)).symm).app X.fiber ≫
          (uC Y.base.unop).op.map f.fiber) ≫
        (eqToHom (congrArg Functor.op (hu g.base.unop)).symm).app Y.fiber ≫
          (uC Z.base.unop).op.map g.fiber
    simp only [Category.assoc, Functor.map_comp]
    rw [NatTrans.naturality_assoc]
    simp [eqToHom_app, eqToHom_map]

/-- Two composites of two `eqToHom`s with the same source and target are equal. Used to
discharge the `eqToHom` bookkeeping left over after the fibre components of a morphism of a
Grothendieck construction have been normalized. -/
private theorem eqToHom_comp_eqToHom {A : Type*} [Category* A] {W X Y Z : A}
    {h₁ : W = X} {h₂ : X = Z} {h₃ : W = Y} {h₄ : Y = Z} :
    eqToHom h₁ ≫ eqToHom h₂ = eqToHom h₃ ≫ eqToHom h₄ := by
  cases h₁
  cases h₂
  simp

private def sectionsToCostructured (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (i : D.I) (X : D.C i) :
    (Over i)ᵒᵖ ⥤ CostructuredArrow (totalToColimit D uC hu) (op ((uC i).obj X)) where
  obj A := CostructuredArrow.mk
    (Y := Grothendieck.mk (F := oppositeSiteDiagram D) (op A.unop.left)
      (op ((D.u A.unop.hom).obj X)))
    (eqToHom (congrArg op (uLeg_eq D uC hu A.unop X).symm))
  map {A B} f := CostructuredArrow.homMk
    (show Grothendieck.mk (F := oppositeSiteDiagram D) (op A.unop.left)
          (op ((D.u A.unop.hom).obj X)) ⟶
        Grothendieck.mk (F := oppositeSiteDiagram D) (op B.unop.left)
          (op ((D.u B.unop.hom).obj X)) from
      { base := f.unop.left.op
        fiber := eqToHom (congrArg op (uObj_eq D f.unop X).symm) }) (by
          change ((eqToHom (congrArg Functor.op (hu f.unop.left)).symm).app
            (op ((D.u A.unop.hom).obj X)) ≫ (uC B.unop.left).op.map
              (eqToHom (congrArg op (uObj_eq D f.unop X).symm))) ≫
                eqToHom (congrArg op (uLeg_eq D uC hu B.unop X).symm) =
              eqToHom (congrArg op (uLeg_eq D uC hu A.unop X).symm)
          rw [eqToHom_app, eqToHom_map]
          simp)
  map_id A := by
    apply CostructuredArrow.hom_ext
    apply Grothendieck.ext _ _ rfl
    simp
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    apply Grothendieck.ext _ _ (by simp)
    simp only [CostructuredArrow.mk_left, Lean.Elab.WF.paramLet, CostructuredArrow.comp_left,
      CostructuredArrow.homMk_left, Grothendieck.comp_base, unop_comp, Over.comp_left, op_comp,
      Grothendieck.comp_fiber, eqToHom_map, eqToHom_trans]
    exact eqToHom_comp_eqToHom

private def sectionsToCostructuredIso (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) (X : D.C i) :
    sectionsToCostructured D uC hu i X ⋙
      CostructuredArrow.proj (totalToColimit D uC hu) (op ((uC i).obj X)) ⋙
      systemPresheafOnTotal D F ≅ sectionsDiagram D F i X := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro A B f
  dsimp [sectionsToCostructured, systemPresheafOnTotal, Grothendieck.functorFrom,
    sectionsDiagram, sectionsMapTo]
  simp


private lemma exists_level_hom_of_hom (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
        (uC j).map g = eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Z).symm)
    (i : D.I) (X : D.C i) (k : D.I) (Y : D.C k)
    (p : (uC i).obj X ⟶ (uC k).obj Y) :
    ∃ (m : D.I) (c : m ⟶ i) (d : m ⟶ k) (g : (D.u c).obj X ⟶ (D.u d).obj Y),
      (uC m).map g = eqToHom (Functor.congr_obj (hu c) X) ≫ p ≫
        eqToHom (Functor.congr_obj (hu d) Y).symm := by
  let n := IsCofiltered.min i k
  let c := IsCofiltered.minToLeft i k
  let d := IsCofiltered.minToRight i k
  obtain ⟨m, e, g, hg⟩ := hhom n ((D.u c).obj X) ((D.u d).obj Y)
    (eqToHom (Functor.congr_obj (hu c) X) ≫ p ≫
      eqToHom (Functor.congr_obj (hu d) Y).symm)
  refine ⟨m, e ≫ c, e ≫ d,
    eqToHom (Functor.congr_obj (D.comp e c) X) ≫ g ≫
      eqToHom (Functor.congr_obj (D.comp e d) Y).symm, ?_⟩
  simp [hg, eqToHom_map]

/-- A morphism followed by two mutually inverse `eqToHom`s is the morphism itself. -/
private theorem comp_eqToHom_eqToHom {C : Type*} [Category* C] {X Y Z : C}
    (f : X ⟶ Y) (p : Y = Z) (q : Z = Y) : (f ≫ eqToHom p) ≫ eqToHom q = f := by
  subst p
  simp

private theorem sectionsToCostructured_exists (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
        (uC j).map g = eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Z).symm)
    (i : D.I) (X : D.C i)
    (P : CostructuredArrow (totalToColimit D uC hu) (op ((uC i).obj X))) :
    ∃ A, Nonempty (P ⟶ (sectionsToCostructured D uC hu i X).obj A) := by
  obtain ⟨m, c, d, g, hg⟩ := exists_level_hom_of_hom D uC hu hhom i X
    P.left.base.unop P.left.fiber.unop P.hom.unop
  refine ⟨op (Over.mk c), ⟨CostructuredArrow.homMk
    (show P.left ⟶ Grothendieck.mk (F := oppositeSiteDiagram D) (op m) (op ((D.u c).obj X)) from
      { base := d.op, fiber := g.op }) ?_⟩⟩
  apply Quiver.Hom.unop_inj
  dsimp [totalToColimit, sectionsToCostructured]
  simp only [eqToHom_unop, hg, Functor.comp_obj, eqToHom_app, Functor.op_obj, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact comp_eqToHom_eqToHom _ _ _

/-- Two morphisms of a Grothendieck construction are equal as soon as their base components
agree and their fibre components are heterogeneously equal. -/
private theorem grothendieck_hom_hext {A : Type*} [Category* A] {T : A ⥤ Cat.{w, w}}
    {X Y : Grothendieck T} {f g : X ⟶ Y} (hb : f.base = g.base) (hf : f.fiber ≍ g.fiber) :
    f = g := by
  obtain ⟨b, φ⟩ := f
  obtain ⟨c, ψ⟩ := g
  dsimp only at hb hf
  subst hb
  rw [eq_of_heq hf]

/-- The fibre component of a composition in a Grothendieck construction, with the structural
`eqToHom` absorbed into a heterogeneous equality. -/
private theorem grothendieck_comp_fiber_heq {A : Type*} [Category* A] {T : A ⥤ Cat.{w, w}}
    {X Y Z : Grothendieck T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber ≍ (T.map g.base).toFunctor.map f.fiber ≫ g.fiber :=
  (heq_of_eq (Grothendieck.comp_fiber f g)).trans (eqToHom_comp_heq _ _)

private theorem total_hom_factor {A : Type*} [Category* A] {T : A ⥤ Cat.{w, w}}
    {X Y : Grothendieck T} (f : X ⟶ Y) :
    X.toTransport f.base ≫ (Grothendieck.ι T Y.base).map f.fiber = f := by
  refine grothendieck_hom_hext (Category.comp_id _)
    ((grothendieck_comp_fiber_heq _ _).trans ?_)
  show (T.map (𝟙 Y.base)).toFunctor.map (𝟙 ((T.map f.base).toFunctor.obj X.fiber)) ≫
    eqToHom _ ≫ f.fiber ≍ f.fiber
  simp

private theorem totalToColimit_eventually_eq_of_base
    (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
      (uC i).map g₁ = (uC i).map g₂ →
        ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
    {X Y : Grothendieck (oppositeSiteDiagram D)} (f g : X ⟶ Y)
    (hb : f.base = g.base) (hf : (totalToColimit D uC hu).map f =
      (totalToColimit D uC hu).map g) :
    ∃ (m : D.I) (a : m ⟶ Y.base.unop),
      f ≫ Y.toTransport a.op = g ≫ Y.toTransport a.op := by
  obtain ⟨b, φ⟩ := f
  obtain ⟨c, ψ⟩ := g
  dsimp at hb
  subst c
  have hf' : (uC Y.base.unop).op.map φ = (uC Y.base.unop).op.map ψ := by
    exact (cancel_epi ((eqToHom (congrArg Functor.op (hu b.unop)).symm).app X.fiber)).mp hf
  have hh : (uC Y.base.unop).map φ.unop = (uC Y.base.unop).map ψ.unop :=
    congrArg Quiver.Hom.unop hf'
  obtain ⟨m, a, ha⟩ := hhom_inj Y.base.unop _ _ φ.unop ψ.unop hh
  have key : ∀ χ : ((oppositeSiteDiagram D).map b).toFunctor.obj X.fiber ⟶ Y.fiber,
      ((⟨b, χ⟩ : X ⟶ Y) ≫ Y.toTransport a.op).fiber ≍
        ((D.u a).map χ.unop).op ≫ 𝟙 (op ((D.u a).obj (unop Y.fiber))) :=
    fun _ => grothendieck_comp_fiber_heq _ _
  exact ⟨m, a, grothendieck_hom_hext rfl
    (((key φ).trans (heq_of_eq (by rw [ha]))).trans (key ψ).symm)⟩

private theorem sectionsToCostructured_final (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
        (uC j).map g = eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Z).symm)
    (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
      (uC i).map g₁ = (uC i).map g₂ →
        ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
    (i : D.I) (X : D.C i) : (sectionsToCostructured D uC hu i X).Final := by
  let T := sectionsToCostructured D uC hu i X
  apply Functor.final_of_exists_of_isFiltered
  · exact sectionsToCostructured_exists D uC hu hhom i X
  · intro P A s s'
    let a := IsCofiltered.eqHom s.left.base.unop s'.left.base.unop
    let A' : (Over i)ᵒᵖ := op (Over.mk (a ≫ A.unop.hom))
    let t : A ⟶ A' := (Over.homMk a).op
    let s₁ := s ≫ T.map t
    let s₂ := s' ≫ T.map t
    have hb : s₁.left.base = s₂.left.base := by
      show s.left.base ≫ a.op = s'.left.base ≫ a.op
      exact congrArg Quiver.Hom.op (IsCofiltered.eq_condition _ _)
    have hi : IsIso (T.obj A').hom :=
      inferInstanceAs
        (IsIso (eqToHom (congrArg op (uLeg_eq D uC hu (Over.mk (a ≫ A.unop.hom)) X).symm)))
    have he : (totalToColimit D uC hu).map s₁.left =
        (totalToColimit D uC hu).map s₂.left := by
      apply (cancel_mono (T.obj A').hom).mp
      simp
    obtain ⟨m, b, hb'⟩ := totalToColimit_eventually_eq_of_base D uC hu hhom_inj
      s₁.left s₂.left hb he
    let A'' : (Over i)ᵒᵖ := op (Over.mk (b ≫ A'.unop.hom))
    let t' : A' ⟶ A'' := (Over.homMk b).op
    refine ⟨A'', t ≫ t', ?_⟩
    show s ≫ T.map (t ≫ t') = s' ≫ T.map (t ≫ t')
    rw [T.map_comp, ← Category.assoc, ← Category.assoc]
    show s₁ ≫ T.map t' = s₂ ≫ T.map t'
    apply CostructuredArrow.hom_ext
    show s₁.left ≫ (T.map t').left = s₂.left ≫ (T.map t').left
    rw [← total_hom_factor (T.map t').left]
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ (Grothendieck.ι (oppositeSiteDiagram D) _).map
        (T.map t').left.fiber) hb')).trans (Category.assoc _ _ _)


private def totalNatTransOfCompatible (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t})
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G) (hι : IsCompatible D uC hu F G ι) :
    systemPresheafOnTotal D F ⟶ totalToColimit D uC hu ⋙ G where
  app X := (ι X.base.unop).app X.fiber
  naturality X Y f := by
    have h := congrArg (fun α => α.app X.fiber) (hι f.base.unop)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    change ((transition D F f.base.unop).app X.fiber ≫
        (F.obj Y.base.unop).obj.map f.fiber) ≫ (ι Y.base.unop).app Y.fiber = _
    rw [Category.assoc, NatTrans.naturality]
    change _ = (ι X.base.unop).app X.fiber ≫
      G.map ((eqToHom (congrArg Functor.op (hu f.base.unop)).symm).app X.fiber ≫
        (uC Y.base.unop).op.map f.fiber)
    rw [h]
    simp [eqToHom_map, Category.assoc]

/-- Every component of `sectionsToCostructuredIso` is an identity morphism. -/
private lemma sectionsToCostructuredIso_hom_app (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) (X : D.C i)
    (A : (Over i)ᵒᵖ) :
    (sectionsToCostructuredIso D uC hu F i X).hom.app A = 𝟙 _ :=
  rfl

private def isColimit_sectionsCocone_of_pointwise
    (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
        (uC j).map g = eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Z).symm)
    (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
      (uC i).map g₁ = (uC i).map g₂ →
        ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t})
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G) (hι : IsCompatible D uC hu F G ι)
    (hKan : (Functor.LeftExtension.mk G
      (totalNatTransOfCompatible D uC hu F G ι hι)).IsPointwiseLeftKanExtension)
    (i : D.I) (X : D.C i) :
    IsColimit (sectionsCocone D uC hu F G ι hι i X) := by
  let T := sectionsToCostructured D uC hu i X
  letI := sectionsToCostructured_final D uC hu hhom hhom_inj i X
  let c := (Functor.LeftExtension.mk G
    (totalNatTransOfCompatible D uC hu F G ι hι)).coconeAt (op ((uC i).obj X))
  let hc : IsColimit (c.whisker T) :=
    (Functor.Final.isColimitWhiskerEquiv T c).symm (hKan _)
  apply (IsColimit.precomposeHomEquiv (sectionsToCostructuredIso D uC hu F i X) _).toFun
  exact IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl _) (fun A => by
    simp only [sectionsToCostructured, Lean.Elab.WF.paramLet, Functor.comp_obj,
      CostructuredArrow.proj_obj, CostructuredArrow.mk_left, sectionsCocone, sectionsMapTo,
      Functor.op_obj, Cocone.precompose_obj_pt, totalNatTransOfCompatible, Cocone.whisker_pt,
      Functor.LeftExtension.coconeAt_pt, Functor.LeftExtension.mk_right, Cocone.whisker_ι,
      Functor.whiskerLeft_app, Functor.LeftExtension.coconeAt_ι_app,
      Functor.whiskeringLeft_obj_obj, Functor.const_obj_obj, Functor.LeftExtension.mk_hom,
      CostructuredArrow.mk_hom_eq_self, Iso.refl_hom, Category.comp_id, Cocone.precompose_obj_ι,
      NatTrans.comp_app, sectionsToCostructuredIso_hom_app, T, c]
    exact (Category.id_comp _).symm))

/-- The colimit `colim fᵢ⁻¹Fᵢ` of a system of abelian sheaves, as a presheaf on the colimit site:
the pointwise left Kan extension, along the functor from the total category of the system to `C`,
of the presheaf on that total category which is `F i` on the fibre over `i`. -/
@[no_expose]
public def systemKanExtension (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) : Cᵒᵖ ⥤ Ab.{max u v w t} :=
  (totalToColimit D uC hu).pointwiseLeftKanExtension (systemPresheafOnTotal D F)


private def totalNatTransStage (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t})
    (α : systemPresheafOnTotal D F ⟶ totalToColimit D uC hu ⋙ G) (i : D.I) :
    (F.obj i).obj ⟶ (uC i).op ⋙ G where
  app V := α.app (Grothendieck.mk (op i) V)
  naturality V W f := by
    have h := α.naturality ((Grothendieck.ι (oppositeSiteDiagram D) (op i)).map f)
    simpa [systemPresheafOnTotal, totalToColimit, Grothendieck.ι,
      transition_id_eqToHom, eqToHom_map, eqToHom_app, oppositeSiteDiagram,
      unop_comp, eqToHom_unop, eqToHom_op, Category.assoc] using h

private theorem totalNatTransStage_compatible (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t})
    (α : systemPresheafOnTotal D F ⟶ totalToColimit D uC hu ⋙ G) :
    IsCompatible D uC hu F G (totalNatTransStage D uC hu F G α) := by
  intro j k a
  apply NatTrans.ext
  funext V
  -- The transport morphism of `V` along `a`, written with its fibre component the identity of
  -- `(D.C k)ᵒᵖ` rather than of the `Cat`-wrapped fibre, so that `Functor.map_id` matches.
  have h := α.naturality (show Grothendieck.mk (F := oppositeSiteDiagram D) (op j) V ⟶
      Grothendieck.mk (F := oppositeSiteDiagram D) (op k) (op ((D.u a).obj V.unop)) from
    { base := a.op, fiber := 𝟙 (op ((D.u a).obj V.unop) : (D.C k)ᵒᵖ) })
  have h' := congrArg (fun z => z ≫ G.map
    (eqToHom (congrArg op (Functor.congr_obj (hu a) V.unop)))) h
  simpa [systemPresheafOnTotal, totalToColimit, totalNatTransStage,
    eqToHom_map, oppositeSiteDiagram, Category.assoc] using h'.symm

private theorem totalNatTransStage_total (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t})
    (α : systemPresheafOnTotal D F ⟶ totalToColimit D uC hu ⋙ G) :
    totalNatTransOfCompatible D uC hu F G (totalNatTransStage D uC hu F G α)
      (totalNatTransStage_compatible D uC hu F G α) = α := by
  ext V
  rfl


private theorem isColimitPresentation_of_pointwise
    (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G.obj)
    (hι : IsCompatible D uC hu F G.obj ι)
    (hKan : (Functor.LeftExtension.mk G.obj
      (totalNatTransOfCompatible D uC hu F G.obj ι hι)).IsPointwiseLeftKanExtension) :
    IsColimitPresentation D uC hu K F G ι := by
  refine ⟨hι, ?_⟩
  intro H g hg
  let α := totalNatTransOfCompatible D uC hu F G.obj ι hι
  let β := totalNatTransOfCompatible D uC hu F H.obj g hg
  let : G.obj.IsLeftKanExtension α := hKan.isLeftKanExtension
  let f : G ⟶ H := ⟨G.obj.descOfIsLeftKanExtension α H.obj β⟩
  have hf : ∀ j, ι j ≫ Functor.whiskerLeft (uC j).op f.hom = g j := by
    intro j
    apply NatTrans.ext
    funext V
    exact G.obj.descOfIsLeftKanExtension_fac_app α H.obj β
      (Grothendieck.mk (op j) V)
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  apply Sheaf.hom_ext
  apply G.obj.hom_ext_of_isLeftKanExtension α
  apply NatTrans.ext
  funext V
  exact (congrArg (fun q => q.app V.fiber) (hf' V.base.unop)).trans
    (congrArg (fun q => q.app V.fiber) (hf V.base.unop)).symm

/-- The map from `F i` to the restriction of `systemKanExtension` along `u_i`: the unit of the
left Kan extension, read on the fibre over `i`. -/
@[no_expose]
public def systemKanUnit (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    (F.obj i).obj ⟶ (uC i).op ⋙ systemKanExtension D uC hu F :=
  totalNatTransStage D uC hu F _
    ((totalToColimit D uC hu).pointwiseLeftKanExtensionUnit (systemPresheafOnTotal D F)) i

private theorem systemKanUnit_compatible (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) :
    IsCompatible D uC hu F (systemKanExtension D uC hu F) (systemKanUnit D uC hu F) :=
  totalNatTransStage_compatible D uC hu F _ _

private def systemKan_isPointwise (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) :
    (Functor.LeftExtension.mk (systemKanExtension D uC hu F)
      (totalNatTransOfCompatible D uC hu F _ (systemKanUnit D uC hu F)
        (systemKanUnit_compatible D uC hu F))).IsPointwiseLeftKanExtension := by
  unfold systemKanUnit systemKanExtension
  rw [totalNatTransStage_total]
  exact Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ _


private theorem stageFunctor_comp (D : InverseSystemOfFiniteSites.{v, u, w})
    {i : D.I} {A B : Over i} (f : A ⟶ B) :
    (D.u B.hom).op ⋙ (D.u f.left).op = (D.u A.hom).op := by
  show (D.u B.hom ⋙ D.u f.left).op = _
  rw [← D.comp, Over.w]

private def stageSectionsMap (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i : D.I} {A B : Over i} (f : A ⟶ B) :
    (D.u B.hom).op ⋙ (F.obj B.left).obj ⟶ (D.u A.hom).op ⋙ (F.obj A.left).obj :=
  Functor.whiskerLeft (D.u B.hom).op (transition D F f.left) ≫
    eqToHom (by rw [← Functor.assoc, stageFunctor_comp D f])

private theorem stageSectionsMap_app (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i : D.I} {A B : Over i} (f : A ⟶ B) (X : (D.C i)ᵒᵖ) :
    (stageSectionsMap D F f).app X = (sectionsDiagram D F i X.unop).map f.op := by
  simp [stageSectionsMap, sectionsDiagram, sectionsMapTo, eqToHom_map]

private def stageSectionsDiagram (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    (Over i)ᵒᵖ ⥤ (D.C i)ᵒᵖ ⥤ Ab.{max u v w t} where
  obj A := (D.u A.unop.hom).op ⋙ (F.obj A.unop.left).obj
  map f := stageSectionsMap D F f.unop
  map_id A := by
    apply NatTrans.ext
    funext X
    simp only [stageSectionsMap_app, Quiver.Hom.op_unop, NatTrans.id_app]
    rw [(sectionsDiagram D F i X.unop).map_id]
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext X
    simp only [stageSectionsMap_app, NatTrans.comp_app, Quiver.Hom.op_unop]
    exact (sectionsDiagram D F i X.unop).map_comp f g

private def stageSectionsLeg (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t}) (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G)
    {i : D.I} (A : Over i) :
    (D.u A.hom).op ⋙ (F.obj A.left).obj ⟶ (uC i).op ⋙ G :=
  Functor.whiskerLeft (D.u A.hom).op (ι A.left) ≫ eqToHom (restrict_eq.{v, u, w, t} D uC hu A.hom G)

private theorem stageSectionsLeg_app (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t}) (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G)
    (hι : IsCompatible D uC hu F G ι) {i : D.I} (A : Over i) (X : (D.C i)ᵒᵖ) :
    (stageSectionsLeg D uC hu F G ι A).app X =
      (sectionsCocone D uC hu F G ι hι i X.unop).ι.app (op A) := by
  simp [stageSectionsLeg, sectionsCocone, sectionsMapTo, eqToHom_map]

private def stageSectionsCocone (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t}) (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G)
    (hι : IsCompatible D uC hu F G ι) (i : D.I) :
    Cocone (stageSectionsDiagram D F i) where
  pt := (uC i).op ⋙ G
  ι := {
    app A := stageSectionsLeg D uC hu F G ι A.unop
    naturality A B f := by
      apply NatTrans.ext
      funext X
      change (stageSectionsMap D F f.unop).app X ≫
        (stageSectionsLeg D uC hu F G ι B.unop).app X =
          (stageSectionsLeg D uC hu F G ι A.unop).app X ≫ 𝟙 _
      rw [Category.comp_id, stageSectionsMap_app,
        stageSectionsLeg_app D uC hu F G ι hι,
        stageSectionsLeg_app D uC hu F G ι hι]
      exact (sectionsCocone D uC hu F G ι hι i X.unop).w f }


private def stageSectionsDiagram_evalIso (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) (X : (D.C i)ᵒᵖ) :
    stageSectionsDiagram D F i ⋙ (evaluation (D.C i)ᵒᵖ (Ab.{max u v w t})).obj X ≅
      sectionsDiagram D F i X.unop := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro A B f
  change (stageSectionsMap D F f.unop).app X ≫ 𝟙 _ =
    𝟙 _ ≫ (sectionsDiagram D F i X.unop).map f
  rw [Category.comp_id, Category.id_comp]
  simpa only [Quiver.Hom.op_unop] using stageSectionsMap_app D F f.unop X

private def isColimit_stageSectionsCocone_of_pointwise
    (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
        (uC j).map g = eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Z).symm)
    (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
      (uC i).map g₁ = (uC i).map g₂ →
        ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (G : Cᵒᵖ ⥤ Ab.{max u v w t})
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G) (hι : IsCompatible D uC hu F G ι)
    (hKan : (Functor.LeftExtension.mk G
      (totalNatTransOfCompatible D uC hu F G ι hι)).IsPointwiseLeftKanExtension) (i : D.I) :
    IsColimit (stageSectionsCocone D uC hu F G ι hι i) := by
  apply evaluationJointlyReflectsColimits
  intro X
  let hc := isColimit_sectionsCocone_of_pointwise D uC hu hhom hhom_inj F G ι hι hKan i X.unop
  apply IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (stageSectionsDiagram_evalIso D F i X) _).symm hc)
  refine Cocone.ext (Iso.refl _) ?_
  intro A
  exact (Category.comp_id _).trans ((Category.id_comp _).trans
    (stageSectionsLeg_app D uC hu F G ι hι A.unop X).symm)

private theorem stageSectionsDiagram_isSheaf (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (i : D.I) (A : (Over i)ᵒᵖ) :
    Presheaf.IsSheaf (D.J i) ((stageSectionsDiagram D F i).obj A) := by
  let := D.continuous A.unop.hom
  exact (((D.u A.unop.hom).sheafPushforwardContinuous (Ab.{max u v w t})
    (D.J i) (D.J A.unop.left)).obj (F.obj A.unop.left)).property

end TotalSite

section FiniteCoverings

universe z

private def multiforkCompEquiv
    {C : Type u} [Category.{v} C] {A B : Type*} [Category* A] [Category* B]
    {X : C} (E : PreOneHypercover.{w} X) (F : Cᵒᵖ ⥤ A) (G : A ⥤ B) :
    IsLimit (G.mapCone (E.multifork F)) ≃ IsLimit (E.multifork (F ⋙ G)) := by
  refine IsLimit.equivOfNatIsoOfIso
    (WalkingMulticospan.functorExt
      (F := (E.multicospanIndex F).multicospan ⋙ G)
      (G := (E.multicospanIndex (F ⋙ G)).multicospan)
      (fun _ => Iso.refl _) (fun _ => Iso.refl _)
      (by intro i; exact (Category.comp_id _).trans (Category.id_comp _).symm)
      (by intro i; exact (Category.comp_id _).trans (Category.id_comp _).symm))
    _ _ (Cone.ext (Iso.refl _) ?_)
  rintro (j | j)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans ((G.map_comp _ _).trans (Category.id_comp _).symm)

private def isLimit_multifork_comp
    {C : Type u} [Category.{v} C] {A B : Type*} [Category* A] [Category* B]
    {X : C} (E : PreOneHypercover.{w} X) (F : Cᵒᵖ ⥤ A) (G : A ⥤ B)
    (h : IsLimit (E.multifork F))
    [PreservesLimit (E.multicospanIndex F).multicospan G] :
    IsLimit (E.multifork (F ⋙ G)) :=
  (multiforkCompEquiv E F G) (isLimitOfPreserves G h)

private def isLimit_multifork_flip
    {C : Type u} [Category.{v} C] {A : Type*} [Category* A]
    {I : Type*} [Category* I] {X : C} (E : PreOneHypercover.{w} X)
    (F : I ⥤ Cᵒᵖ ⥤ A) (h : ∀ i, IsLimit (E.multifork (F.obj i))) :
    IsLimit (E.multifork F.flip) :=
  evaluationJointlyReflectsLimits _ (fun i =>
    (multiforkCompEquiv E F.flip ((evaluation I A).obj i)).symm (h i))

private def multiforkIsoEquiv
    {C : Type u} [Category.{v} C] {A : Type*} [Category* A]
    {X : C} (E : PreOneHypercover.{w} X) {F G : Cᵒᵖ ⥤ A} (e : F ≅ G) :
    IsLimit (E.multifork F) ≃ IsLimit (E.multifork G) :=
  Multifork.isLimitEquivOfIsos _ _ (e.app (op X))
    (fun i => e.app (op (E.X i))) (fun j => e.app (op (E.Y j.2)))
    (fun _j => e.hom.naturality _) (fun _j => e.hom.naturality _)
    (fun _i => (e.hom.naturality _).symm)

private def isLimit_multifork_colimit
    {C : Type u} [Category.{v} C] {A : Type*} [Category* A]
    {I : Type*} [Category* I] [HasColimitsOfShape I A]
    [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)]
    {X : C} (E : PreOneHypercover.{w} X) [Finite E.I₀] [∀ i j, Finite (E.I₁ i j)]
    (F : I ⥤ Cᵒᵖ ⥤ A) (h : ∀ i, IsLimit (E.multifork (F.obj i))) :
    IsLimit (E.multifork (colimit F)) := by
  classical
  letI : Fintype E.multicospanShape.L := Fintype.ofFinite E.I₀
  letI : Fintype E.multicospanShape.R := Fintype.ofFinite E.I₁'
  exact (multiforkIsoEquiv E (colimitIsoFlipCompColim F)).symm
    (isLimit_multifork_comp E F.flip colim (isLimit_multifork_flip E F h))

private def isLimit_multifork_of_isColimit
    {C : Type u} [Category.{v} C] {A : Type*} [Category* A]
    {I : Type*} [Category* I] [HasColimitsOfShape I A]
    [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)]
    {X : C} (E : PreOneHypercover.{w} X) [Finite E.I₀] [∀ i j, Finite (E.I₁ i j)]
    (F : I ⥤ Cᵒᵖ ⥤ A) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ i, IsLimit (E.multifork (F.obj i))) : IsLimit (E.multifork c.pt) :=
  multiforkIsoEquiv E ((colimit.isColimit F).coconePointUniqueUpToIso hc)
    (isLimit_multifork_colimit E F h)

private theorem isSheafFor_of_isColimit
    {C : Type u} [Category.{v} C] {I : Type*} [Category* I]
    [HasColimitsOfShape I (Type z)] [PreservesFiniteLimits (colim : (I ⥤ Type z) ⥤ Type z)]
    {X : C} (E : PreZeroHypercover.{w} X) [Finite E.I₀] [E.HasPullbacks]
    (F : I ⥤ Cᵒᵖ ⥤ Type z) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ i, E.presieve₀.IsSheafFor (F.obj i)) : E.presieve₀.IsSheafFor c.pt := by
  let : Finite E.toPreOneHypercover.I₀ := inferInstanceAs (Finite E.I₀)
  let (i j : E.toPreOneHypercover.I₀) : Finite (E.toPreOneHypercover.I₁ i j) := by
    dsimp [PreZeroHypercover.toPreOneHypercover]
    infer_instance
  exact (E.isLimit_toPreOneHypercover_type_iff c.pt).mp
    ⟨isLimit_multifork_of_isColimit E.toPreOneHypercover F c hc
      (fun i => ((E.isLimit_toPreOneHypercover_type_iff (F.obj i)).mpr (h i)).some)⟩

private theorem isSheafFor_map_of_isSheafFor_comp
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    (P : Dᵒᵖ ⥤ Type z) {X : C} (R : Presieve X)
    (h : R.IsSheafFor (G.op ⋙ P)) : (R.map G).IsSheafFor P := by
  intro x hx
  let x' : R.FamilyOfElements (G.op ⋙ P) := fun _ f hf => x (G.map f) (.of hf)
  have hx' : x'.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ he
    exact hx (G.map g₁) (G.map g₂) (.of h₁) (.of h₂)
      (by simpa using congrArg G.map he)
  obtain ⟨t, ht, ht'⟩ := h x' hx'
  refine ⟨t, ?_, ?_⟩
  · intro Y f hf
    cases hf with
    | of hf => exact ht _ hf
  · intro t' ht''
    apply ht'
    intro Y f hf
    exact ht'' _ (.of hf)

private def finiteCoverage {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (hfinite : ∀ {X : C} (S : Sieve X), S ∈ J X →
      ∃ R : Presieve X, R ≤ S.arrows ∧ R ∈ J.toPrecoverage X ∧
        R ∈ Precoverage.finite C X) : Coverage C where
  __ := J.toPrecoverage ⊓ Precoverage.finite C
  pullback := by
    intro X Y f R hR
    obtain ⟨T, hT, hTJ, hTf⟩ := hfinite _ (J.pullback_stable f hR.1)
    exact ⟨T, ⟨hTJ, hTf⟩, fun Z g hg => hT Z g hg⟩

private theorem finiteCoverage_toGrothendieck {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (hfinite : ∀ {X : C} (S : Sieve X), S ∈ J X →
      ∃ R : Presieve X, R ≤ S.arrows ∧ R ∈ J.toPrecoverage X ∧
        R ∈ Precoverage.finite C X) : (finiteCoverage J hfinite).toGrothendieck = J := by
  rw [← Coverage.toGrothendieck_toPrecoverage]
  apply le_antisymm
  · exact (Precoverage.toGrothendieck_le_iff_le_toPrecoverage).mpr inf_le_left
  · intro X S hS
    obtain ⟨R, hRS, hRJ, hRf⟩ := hfinite S hS
    apply GrothendieckTopology.superset_covering _ (Sieve.generate_le_iff R S |>.mpr hRS)
    exact Precoverage.generate_mem_toGrothendieck (J := (finiteCoverage J hfinite).toPrecoverage)
      ⟨hRJ, hRf⟩

private theorem isSheaf_of_isColimit_finiteCoverings
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (hfinite : ∀ {X : C} (S : Sieve X), S ∈ J X →
      ∃ R : Presieve X, R ≤ S.arrows ∧ R ∈ J.toPrecoverage X ∧
        R ∈ Precoverage.finite C X)
    [(J.toPrecoverage ⊓ Precoverage.finite C).HasPullbacks]
    {I : Type*} [Category* I] [HasColimitsOfShape I (Type z)]
    [PreservesFiniteLimits (colim : (I ⥤ Type z) ⥤ Type z)]
    (F : I ⥤ Cᵒᵖ ⥤ Type z) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, Presieve.IsSheaf J (F.obj i)) : Presieve.IsSheaf J c.pt := by
  rw [← finiteCoverage_toGrothendieck J hfinite, Presieve.isSheaf_coverage]
  intro X R hR
  let E : PreZeroHypercover.{max u v} X := {
    I₀ := R.uncurry
    X r := r.1.1
    f r := r.1.2 }
  have he : E.presieve₀ = R := by
    funext Y f
    apply propext
    constructor
    · rintro ⟨r⟩
      exact r.2
    · intro hf
      exact Presieve.ofArrows.mk (show E.I₀ from ⟨⟨Y, f⟩, hf⟩)
  let : Fintype E.I₀ := hR.2.fintype
  let : E.presieve₀.HasPairwisePullbacks := he ▸
    Precoverage.hasPairwisePullbacks_of_mem
      (J.toPrecoverage ⊓ Precoverage.finite C) hR
  let : E.HasPullbacks := by infer_instance
  rw [← he]
  apply isSheafFor_of_isColimit E F c hc
  intro i
  rw [he, Presieve.isSheafFor_iff_generate]
  exact hF i _ hR.1

private theorem abelian_isSheaf_of_isColimit_finiteCoverings
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (hfinite : ∀ {X : C} (S : Sieve X), S ∈ J X →
      ∃ R : Presieve X, R ≤ S.arrows ∧ R ∈ J.toPrecoverage X ∧
        R ∈ Precoverage.finite C X)
    [(J.toPrecoverage ⊓ Precoverage.finite C).HasPullbacks]
    {I : Type*} [Category* I] [HasColimitsOfShape I (Type (max w z))]
    [PreservesFiniteLimits (colim : (I ⥤ Type (max w z)) ⥤ Type (max w z))]
    [HasColimitsOfShape I (Ab.{max w z})]
    [PreservesColimitsOfShape I (forget (Ab.{max w z}))]
    (F : I ⥤ Cᵒᵖ ⥤ Ab.{max w z}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, Presheaf.IsSheaf J (F.obj i)) : Presheaf.IsSheaf J c.pt := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp J c.pt (forget (Ab.{max w z})),
    isSheaf_iff_isSheaf_of_type]
  let T := (Functor.whiskeringRight Cᵒᵖ (Ab.{max w z}) (Type (max w z))).obj
    (forget (Ab.{max w z}))
  apply isSheaf_of_isColimit_finiteCoverings J hfinite (F ⋙ T) (T.mapCocone c)
    (isColimitOfPreserves T hc)
  intro i
  exact (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf J (F.obj i) (forget (Ab.{max w z})) (hF i))

private theorem isSheaf_of_restriction (D : InverseSystemOfFiniteSites.{v, u, w})
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
    (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
        (uC j).map g = eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Z).symm)
    (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
      (uC i).map g₁ = (uC i).map g₂ →
        ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
    (K : Precoverage C)
    (hK : ∀ (Y : C) (R : Presieve Y), R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
    (P : Cᵒᵖ ⥤ Type z)
    (hP : ∀ i, Presieve.IsSheaf (D.J i) ((uC i).op ⋙ P)) :
    Presieve.IsSheaf K.toGrothendieck P := by
  obtain ⟨K', hK', _, _, hPB, hcov⟩ :=
    CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.exists_precoverage_of_colimit
      D uC hu hobj hhom hhom_inj
  obtain rfl : K = K' :=
    Precoverage.ext (funext fun Y => Set.ext fun R => (hK Y R).trans (hK' Y R).symm)
  let : K.HasPullbacks := hPB
  let Kc : Coverage C := {
    __ := K
    pullback := by
      intro X Y f R hR
      let := K.hasPullbacks_of_mem f hR
      exact ⟨R.pullbackArrows f, hcov X Y f R hR,
        Presieve.FactorsThruAlong.pullbackArrows f R⟩ }
  have he : K.toGrothendieck = Kc.toGrothendieck := Kc.toGrothendieck_toPrecoverage
  rw [he, Presieve.isSheaf_coverage]
  intro Y R hR
  obtain ⟨i, Z, rfl, S, hS, _, rfl⟩ := (hK Y R).mp hR
  apply isSheafFor_map_of_isSheafFor_comp (uC i) P S
  rw [Presieve.isSheafFor_iff_generate]
  exact hP i _ hS

end FiniteCoverings

section KanSheaf
variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))

variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)

include hobj hhom hhom_inj hK in
/-- **`systemKanExtension` is a sheaf.** Its restriction to each level is a colimit of sheaves of
a shape that commutes with finite limits, hence a sheaf, the coverings of that level being refined
by finite ones; and a presheaf on the colimit site whose restrictions to all levels are sheaves is
a sheaf. -/
public theorem systemKanExtension_isSheaf :
    Presheaf.IsSheaf K.toGrothendieck (systemKanExtension D uC hu F) := by
  let : PreservesFilteredColimitsOfSize.{v, max u v}
      (forget (Ab.{max u v w t})) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w t, max u v w t} _
  have hstage (i : D.I) : Presheaf.IsSheaf (D.J i)
      ((uC i).op ⋙ systemKanExtension D uC hu F) := by
    let := D.hasPullbacks i
    exact abelian_isSheaf_of_isColimit_finiteCoverings (D.J i)
      (D.finiteCoverings i)
      (stageSectionsDiagram D F i)
      (stageSectionsCocone D uC hu F _ (systemKanUnit D uC hu F)
        (systemKanUnit_compatible D uC hu F) i)
      (isColimit_stageSectionsCocone_of_pointwise D uC hu hhom hhom_inj F _
        (systemKanUnit D uC hu F) (systemKanUnit_compatible D uC hu F)
        (systemKan_isPointwise D uC hu F) i)
      (stageSectionsDiagram_isSheaf D F i)
  rw [Presheaf.isSheaf_iff_isSheaf_comp K.toGrothendieck _ (forget (Ab.{max u v w t})),
    isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_restriction D uC hu hobj hhom hhom_inj K hK
  intro i
  exact (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf (D.J i) _ (forget (Ab.{max u v w t})) (hstage i))

/-- The colimit `colim fᵢ⁻¹Fᵢ` of a system of abelian sheaves, as an abelian sheaf on the colimit
site: `systemKanExtension` together with `systemKanExtension_isSheaf`. -/
public def systemColimitSheaf : Sheaf K.toGrothendieck (Ab.{max u v w t}) :=
  ⟨systemKanExtension D uC hu F,
    systemKanExtension_isSheaf D uC hu hobj hhom hhom_inj K hK F⟩

include hobj hhom hhom_inj hK in
attribute [local instance_reducible] systemColimitSheaf

/-- `systemColimitSheaf`, with the maps `systemKanUnit`, is a colimit presentation of the system
in the sense of `IsColimitPresentation`. -/
public theorem systemColimitSheaf_isColimitPresentation :
    IsColimitPresentation D uC hu K F
      (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) (systemKanUnit D uC hu F) :=
  isColimitPresentation_of_pointwise D uC hu K F _ _
    (systemKanUnit_compatible D uC hu F) (systemKan_isPointwise D uC hu F)


/-- **Colimit presentations are unique up to isomorphism.** Two colimit presentations `(G, ιG)`
and `(H, ιH)` of the same system are isomorphic, by an isomorphism carrying `ιG` to `ιH`. -/
public theorem colimitPresentation_uniqueIso
    (G H : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ιG : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G.obj)
    (ιH : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ H.obj)
    (hG : IsColimitPresentation D uC hu K F G ιG)
    (hH : IsColimitPresentation D uC hu K F H ιH) :
    ∃ e : G ≅ H, ∀ j, ιG j ≫ Functor.whiskerLeft (uC j).op e.hom.hom = ιH j := by
  obtain ⟨f, hf, _⟩ := hG.2 H ιH hH.1
  obtain ⟨g, hg, _⟩ := hH.2 G ιG hG.1
  have hfg : f ≫ g = 𝟙 G := by
    obtain ⟨l, _, hl⟩ := hG.2 G ιG hG.1
    apply (hl _ ?_).trans (hl _ ?_).symm
    · intro j
      show ιG j ≫ Functor.whiskerLeft (uC j).op (f.hom ≫ g.hom) = _
      rw [Functor.whiskerLeft_comp, ← Category.assoc, hf, hg]
    · intro j
      simp
  have hgf : g ≫ f = 𝟙 H := by
    obtain ⟨l, _, hl⟩ := hH.2 H ιH hH.1
    apply (hl _ ?_).trans (hl _ ?_).symm
    · intro j
      show ιH j ≫ Functor.whiskerLeft (uC j).op (g.hom ≫ f.hom) = _
      rw [Functor.whiskerLeft_comp, ← Category.assoc, hg, hf]
    · intro j
      simp
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

include hobj hhom hhom_inj hK in
private def isColimit_sectionsCocone_of_presentation
    (G : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G.obj)
    (hG : IsColimitPresentation D uC hu K F G ι) (i : D.I) (X : D.C i) :
    IsColimit (sectionsCocone D uC hu F G.obj ι hG.1 i X) := by
  let H := systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F
  have hex := colimitPresentation_uniqueIso D uC hu K F H G
    (systemKanUnit D uC hu F) ι
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F) hG
  let e := Classical.choose hex
  have he := Classical.choose_spec hex
  apply IsColimit.ofIsoColimit
    (isColimit_sectionsCocone_of_pointwise D uC hu hhom hhom_inj F _
      (systemKanUnit D uC hu F) (systemKanUnit_compatible D uC hu F)
      (systemKan_isPointwise D uC hu F) i X)
  refine Cocone.ext (((sheafSections K.toGrothendieck (Ab.{max u v w t})).obj
    (op ((uC i).obj X))).mapIso e) ?_
  intro A
  have h := congrArg (fun q => q.app (op ((D.u A.unop.hom).obj X))) (he A.unop.left)
  change ((systemKanUnit D uC hu F A.unop.left).app (op ((D.u A.unop.hom).obj X)) ≫
    H.obj.map (eqToHom (congrArg op (uLeg_eq D uC hu A.unop X).symm))) ≫
      e.hom.hom.app (op ((uC i).obj X)) = _
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [Category.assoc, NatTrans.naturality, ← Category.assoc]
  exact congrArg (fun q => q ≫ G.obj.map
    (eqToHom (congrArg op (uLeg_eq D uC hu A.unop X).symm))) h

end KanSheaf

end Stacks.WeakSites.ColimitSiteCohomology

end
