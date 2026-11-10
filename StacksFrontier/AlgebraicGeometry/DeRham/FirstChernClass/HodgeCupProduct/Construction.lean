module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift

/-!
# The cup product on Hodge cohomology: construction

The sheaves of differential forms `Ω^p` placed in degree `0`, their wedge product, the
identification of Hodge cohomology with the hypercohomology of `Ω^p[0]`, the cup product
`AlgebraicGeometry.SheafOfModules.hodgeCup` on Hodge cohomology (Tag 0FM4), and the
identification `gradedPieceShiftIso` of the graded pieces with shifts of `Ω^k[0]`, compatible
with the multiplications (`multiplicationInt_gradedPieceWedge_shift`).

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The sheaves of differential forms placed in degree zero and their wedge product -/

/-- **`Ω^p_{𝒪_X/A}[0]`**, the sheaf of relative `p`-forms placed in cohomological degree `0`. -/
abbrev hodgeSingle (p : ℕ) :
    CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ :=
  (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj ((deRhamComplex B D).X p)

/-- `Tot(Ω^p[0] ⊗_A Ω^q[0])` vanishes in every positive degree. -/
lemma isZero_hodgeSingleTensor_X (p q n : ℕ) (hn : n ≠ 0) :
    IsZero ((((tensorBifunctorNat (A := A)).obj (hodgeSingle B D p)).obj
      (hodgeSingle B D q)).X n) := by
  change IsZero ((HomologicalComplex.mapBifunctor (hodgeSingle B D p)
    (hodgeSingle B D q) (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ)).X n)
  refine HomologicalComplex₂.isZero_total_X_of_isZero _ _ n fun a b hab => ?_
  have hab' : a + b = n := hab
  change IsZero (((sheafTensor.{u, u, u, u, u} A).obj ((hodgeSingle B D p).X a)).obj
    ((hodgeSingle B D q).X b))
  by_cases ha : a = 0
  · exact isZero_tensorFunctor_obj_obj_of_right _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 _ b (by omega))
  · exact isZero_tensorFunctor_obj_obj_of_left
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 _ a ha) _

/-- The component of the wedge product of `Ω^p[0]` and `Ω^q[0]` on the `(a, b)` summand of the
degree-`0` term of their total tensor complex, which forces `a = b = 0`: wedge multiplication of a
`p`-form by a `q`-form. -/
def hodgeSingleWedgeSummand (p q a b : ℕ) (hab : a + b = 0) :
    ((sheafTensor.{u, u, u, u, u} A).obj ((hodgeSingle B D p).X a)).obj
        ((hodgeSingle B D q).X b) ⟶
      (deRhamComplex B D).X (p + q) :=
  ((sheafTensor.{u, u, u, u, u} A).obj ((hodgeSingle B D p).X a)).map
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X q) b
          (by omega)).hom ≫
    ((sheafTensor.{u, u, u, u, u} A).map
          (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X p) a
            (by omega)).hom).app ((deRhamComplex B D).X q) ≫
      exteriorProductComponent B p q

/-- **The wedge product `Tot(Ω^p[0] ⊗_A Ω^q[0]) ⟶ Ω^{p + q}[0]`** induced by the wedge
multiplication `Ω^p ⊗_A Ω^q ⟶ Ω^{p + q}` of Tag 0FM2. Source and target are concentrated in
degree `0`, so its degree-`0` component determines it. -/
def hodgeSingleWedge (p q : ℕ) :
    ((tensorBifunctorNat (A := A)).obj (hodgeSingle B D p)).obj (hodgeSingle B D q) ⟶
      hodgeSingle B D (p + q) :=
  HomologicalComplex.mkHomToSingle
    (HomologicalComplex.mapBifunctorDesc fun a b h => hodgeSingleWedgeSummand B D p q a b h)
    fun i hi => by
      change i + 1 = 0 at hi
      omega

/-! ### Hodge cohomology as the hypercohomology of a complex in degree zero -/

/-- The sheaf `Ω^p` read in abelian sheaves and placed in degree `0` is the abelianisation of
`Ω^p[0]`, extended by zero. -/
def hodgeSinglePlusIso (p : ℕ) :
    (Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).obj
        ((deRhamAbelianComplex B D).X p) ≅ modulePlus (A := A) (hodgeSingle B D p) :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.extendSingleIso embeddingUpNat ((deRhamAbelianComplex B D).X p) 0 0
        rfl).symm ≪≫
      (embeddingUpNat.extendFunctor (AbelianSheaf X.carrier)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A))
          (ComplexShape.up ℕ) 0).app ((deRhamComplex B D).X p)).symm)

/-- **`H^i(X, Ω^p) ≅ H^i(X, Ω^p[0])`**: the `i`-th right derived functor of global sections at
`Ω^p` is the degree-`i` hypercohomology of `Ω^p` placed in degree `0`, through the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the two indexings of the right derived functors. The
degree is a parameter constrained by `hn`, so that it can be read off a sum. -/
def hodgeSingleCohomologyIso (p i : ℕ) (n : ℤ) (hn : (i : ℤ) = n) :
    ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p) ≅
      moduleHypercohomology (A := A) (hodgeSingle B D p) n := by
  subst hn
  exact (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X.carrier ⊤) i).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).mapIso
      ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.mapIso
        (DerivedCategory.Plus.Q.mapIso (hodgeSinglePlusIso B D p)))

/-! ### The cup product on Hodge cohomology -/

/-- **Stacks Project, Tag 0FM4.** **The cup product on Hodge cohomology**

`∪ : H^i(X, Ω^p_{𝒪_X/A}) × H^j(X, Ω^q_{𝒪_X/A}) ⟶ H^{i + j}(X, Ω^{p + q}_{𝒪_X/A})`:

the cup product of Cohomology, Section 0FKU along the wedge product
`Ω^p[0] ⊗_A Ω^q[0] ⟶ Ω^{p + q}[0]` of Tag 0FM2 (`AlgebraicGeometry.SheafOfModules.canonicalPairing`
along `AlgebraicGeometry.SheafOfModules.hodgeSingleWedge`), read through
`AlgebraicGeometry.SheafOfModules.hodgeSingleCohomologyIso`. It has no parameter. The indices of
the target are parameters constrained by `hr` and `hl`, so that a caller obtains the product in
the group it is holding. -/
def hodgeCup (p q r : ℕ) (hr : p + q = r) (i j l : ℕ) (hl : i + j = l) :
    ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p) →
      ((sectionsFunctor X.carrier ⊤).rightDerived j).obj ((deRhamAbelianComplex B D).X q) →
        ((sectionsFunctor X.carrier ⊤).rightDerived l).obj ((deRhamAbelianComplex B D).X r) := by
  subst hr hl
  exact fun x y => (hodgeSingleCohomologyIso B D (p + q) (i + j) ((i : ℤ) + (j : ℤ))
    (by push_cast; rfl)).inv.hom (canonicalPairing (hodgeSingleWedge B D p q) (i : ℤ) (j : ℤ)
      ((hodgeSingleCohomologyIso B D p i i rfl).hom.hom x)
      ((hodgeSingleCohomologyIso B D q j j rfl).hom.hom y))

/-- The Hodge cup product, at the indices it is built at. -/
theorem hodgeCup_eq (p q i j : ℕ)
    (x : ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p))
    (y : ((sectionsFunctor X.carrier ⊤).rightDerived j).obj ((deRhamAbelianComplex B D).X q)) :
    hodgeCup B D p q (p + q) rfl i j (i + j) rfl x y =
      (hodgeSingleCohomologyIso B D (p + q) (i + j) ((i : ℤ) + (j : ℤ))
        (by push_cast; rfl)).inv.hom (canonicalPairing (hodgeSingleWedge B D p q) (i : ℤ) (j : ℤ)
          ((hodgeSingleCohomologyIso B D p i i rfl).hom.hom x)
          ((hodgeSingleCohomologyIso B D q j j rfl).hom.hom y)) :=
  rfl

/-! ### The graded pieces as shifts of the sheaves of forms in degree zero -/

/-- Moving the degree of a component of a morphism of complexes across identifications of
objects. -/
@[reassoc]
lemma eqToHom_comp_f_eq {V : Type*} [Category* V] [HasZeroMorphisms V]
    {K L : CochainComplex V ℤ} (φ : K ⟶ L) (n d : ℤ) (h : n = d) {Y : V} (e : Y = K.X d) :
    eqToHom e ≫ φ.f d =
      eqToHom (e.trans (congrArg K.X h.symm)) ≫ φ.f n ≫ eqToHom (congrArg L.X h) := by
  subst h
  simp

/-- The algebra of `ι_multiplicationInt_f`, with every object and morphism a variable. -/
lemma extend_paste {V : Type*} [Category* V] {a x₁ x₂ y b c z d : V} (ι : a ⟶ b) (E : b ⟶ c)
    (G : c ⟶ d) (X₁ : a ⟶ x₁) (X₂ : x₁ ⟶ x₂) (ι' : x₂ ⟶ y) (e : c ≅ y) (m : y ⟶ z) (w : z ⟶ d)
    (e' : c ≅ y) (h₁ : ι ≫ E = X₁ ≫ X₂ ≫ ι' ≫ e.inv) (h₂ : G = e'.hom ≫ m ≫ w) (he : e = e') :
    ι ≫ E ≫ G = X₁ ≫ X₂ ≫ ι' ≫ m ≫ w := by
  subst he
  rw [← Category.assoc, h₁, h₂]
  simp

/-- The component of an extended multiplication on a summand of nonnegative bidegree: the
multiplication on the summand of the same bidegree, read through the identifications of the
extensions. -/
@[reassoc]
lemma ι_multiplicationInt_f {K L M : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) (n p q : ℕ)
    (h : (p : ℤ) + (q : ℤ) = (n : ℤ)) :
    HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ) p q (n : ℤ) h ≫
        (multiplicationInt m).f (n : ℤ) =
      ((sheafTensor.{u, u, u, u, u} A).map
          (K.extendXIso embeddingUpNat (i' := (p : ℤ)) (i := p) (by simp)).hom).app _ ≫
        ((sheafTensor.{u, u, u, u, u} A).obj (K.X p)).map
          (L.extendXIso embeddingUpNat (i' := (q : ℤ)) (i := q) (by simp)).hom ≫
        HomologicalComplex.ιMapBifunctor K L (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ)
          p q n (by dsimp; omega) ≫
        m.f n ≫ (M.extendXIso embeddingUpNat (i' := (n : ℤ)) (i := n) (by simp)).inv := by
  have h₁ := HomologicalComplex.ι_mapBifunctorExtendHom_f
      (sheafTensor.{u, u, u, u, u} A) K L n p q h
  have h₂ := HomologicalComplex.extendMap_f m embeddingUpNat (i := n) (i' := (n : ℤ)) rfl
  exact extend_paste _ _ _ _ _ _ _ _ _ _ h₁ h₂ rfl

/-- The components of the inverse of the comparison of the single functors with the shift are
identifications of objects. -/
lemma singleFunctors_shiftIso_inv_app_f {V : Type*} [Category* V] [Preadditive V]
    [HasZeroObject V] (n a a' : ℤ) (h : n + a = a') (Z : V) (i : ℤ)
    (e : ((CochainComplex.singleFunctor V a).obj Z).X i =
      ((shiftFunctor (CochainComplex V ℤ) n).obj ((CochainComplex.singleFunctor V a').obj Z)).X i) :
    (((CochainComplex.singleFunctors V).shiftIso n a a' h).inv.app Z).f i = eqToHom e := rfl

/-- **`Ω^k[-k] ≅ Ω^k[0][-k]`**: the graded piece `Ω^k_{𝒪_X/A}[-k]`, extended by zero, is the shift
by `-k` of `Ω^k_{𝒪_X/A}[0]`, extended by zero. -/
def gradedPieceShiftIso (k : ℕ) :
    (deRhamGradedPiece B D k).extend embeddingUpNat ≅
      ((hodgeSingle B D k).extend embeddingUpNat)⟦-(k : ℤ)⟧ :=
  HomologicalComplex.extendSingleIso embeddingUpNat ((deRhamComplex B D).X k) k (k : ℤ) rfl ≪≫
    ((CochainComplex.singleFunctors _).shiftIso (-(k : ℤ)) (k : ℤ) 0 (by omega)).symm.app
      ((deRhamComplex B D).X k) ≪≫
    (CategoryTheory.shiftFunctor _ (-(k : ℤ))).mapIso
      (HomologicalComplex.extendSingleIso embeddingUpNat ((deRhamComplex B D).X k) 0 0 rfl).symm

/-- `Ω^k[-k]`, extended by zero, vanishes outside degree `k`. -/
lemma isZero_gradedPiece_extend_X (k : ℕ) (n : ℤ) (hn : n ≠ (k : ℤ)) :
    IsZero (((deRhamGradedPiece B D k).extend embeddingUpNat).X n) :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (k : ℤ) _ n hn).of_iso
    ((HomologicalComplex.eval _ _ n).mapIso
      (HomologicalComplex.extendSingleIso embeddingUpNat ((deRhamComplex B D).X k) k (k : ℤ) rfl))

/-- A composite of identifications of objects is one. -/
lemma exists_eqToHom_comp {V : Type*} [Category* V] {a b c : V} {f : a ⟶ b} {g : b ⟶ c}
    (hf : ∃ h, f = eqToHom h) (hg : ∃ h, g = eqToHom h) : ∃ h, f ≫ g = eqToHom h := by
  obtain ⟨h₁, rfl⟩ := hf
  obtain ⟨h₂, rfl⟩ := hg
  exact ⟨_, eqToHom_trans _ _⟩

section Sandwich

variable {V : Type*} [Category* V]

/-- `L` is `f` up to identifications of objects on both sides. -/
def IsEqToHomSandwich {a b c d : V} (f : b ⟶ c) (L : a ⟶ d) : Prop :=
  ∃ (h : a = b) (h' : c = d), L = eqToHom h ≫ f ≫ eqToHom h'

/-- Two morphisms that are both `f` up to identifications of objects are equal. -/
lemma IsEqToHomSandwich.eq {a b c d : V} {f : b ⟶ c} {L R : a ⟶ d}
    (hL : IsEqToHomSandwich f L) (hR : IsEqToHomSandwich f R) : L = R := by
  obtain ⟨_, _, rfl⟩ := hL
  obtain ⟨_, _, rfl⟩ := hR
  rfl

/-- Every morphism `f` is itself up to identifications of objects. -/
lemma IsEqToHomSandwich.self {b c : V} (f : b ⟶ c) : IsEqToHomSandwich f f :=
  ⟨rfl, rfl, by simp⟩

/-- Precomposing with an `eqToHom` preserves `IsEqToHomSandwich f`. -/
lemma IsEqToHomSandwich.pre {a a' b c d : V} {f : b ⟶ c} {x : a ⟶ a'} {r : a' ⟶ d}
    (hx : ∃ h, x = eqToHom h) (hr : IsEqToHomSandwich f r) : IsEqToHomSandwich f (x ≫ r) := by
  obtain ⟨h, rfl⟩ := hx
  obtain ⟨h₁, h₂, rfl⟩ := hr
  exact ⟨h.trans h₁, h₂, by simp⟩

/-- Postcomposing with an `eqToHom` preserves `IsEqToHomSandwich f`. -/
lemma IsEqToHomSandwich.post {a b c d d' : V} {f : b ⟶ c} {l : a ⟶ d} {y : d ⟶ d'}
    (hl : IsEqToHomSandwich f l) (hy : ∃ h, y = eqToHom h) : IsEqToHomSandwich f (l ≫ y) := by
  obtain ⟨h, rfl⟩ := hy
  obtain ⟨h₁, h₂, rfl⟩ := hl
  exact ⟨h₁, h₂.trans h, by simp⟩

/-- `IsEqToHomSandwich f` is invariant under reassociating a triple composite. -/
lemma IsEqToHomSandwich.assoc {a m n d b c : V} {f : b ⟶ c} {x : a ⟶ m} {y : m ⟶ n}
    {z : n ⟶ d} (h : IsEqToHomSandwich f ((x ≫ y) ≫ z)) :
    IsEqToHomSandwich f (x ≫ y ≫ z) := by
  rwa [← Category.assoc]

/-- Postcomposing the last factor of `x ≫ y` with an `eqToHom` preserves `IsEqToHomSandwich f`. -/
private lemma IsEqToHomSandwich.assoc_post {a m n d b c : V} {f : b ⟶ c} {x : a ⟶ m} {y : m ⟶ n}
    {z : n ⟶ d} (h : IsEqToHomSandwich f (x ≫ y)) (hz : ∃ h, z = eqToHom h) :
    IsEqToHomSandwich f (x ≫ y ≫ z) :=
  (h.post hz).assoc

/-- `IsEqToHomSandwich f` transported along an equality of morphisms. -/
lemma IsEqToHomSandwich.of_eq {a b c d : V} {f : b ⟶ c} {L L' : a ⟶ d} (e : L = L')
    (h : IsEqToHomSandwich f L') : IsEqToHomSandwich f L := e ▸ h

/-- A functor sends an `eqToHom` morphism to an `eqToHom` morphism. -/
lemma exists_eqToHom_map {W : Type*} [Category* W] (F : V ⥤ W) {a b : V} {x : a ⟶ b}
    (hx : ∃ h, x = eqToHom h) : ∃ h, F.map x = eqToHom h := by
  obtain ⟨h, rfl⟩ := hx
  exact ⟨_, eqToHom_map F h⟩

/-- The components of an `eqToHom` natural transformation are `eqToHom` morphisms. -/
lemma exists_eqToHom_app {W : Type*} [Category* W] {F G : V ⥤ W} {α : F ⟶ G}
    (hα : ∃ h, α = eqToHom h) (Y : V) : ∃ h, α.app Y = eqToHom h := by
  obtain ⟨h, rfl⟩ := hα
  exact ⟨_, eqToHom_app h Y⟩

/-- The identification `singleObjXIsoOfEq` of the degree `i = j` term of a single complex is an
`eqToHom`. -/
lemma exists_eqToHom_singleObjXIsoOfEq_hom {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}
    [HasZeroMorphisms V] [HasZeroObject V] (j : ι) (A : V) (i : ι) (hi : i = j) :
    ∃ h, (HomologicalComplex.singleObjXIsoOfEq c j A i hi).hom = eqToHom h := by
  subst hi
  exact ⟨HomologicalComplex.single_obj_X_self c i A, rfl⟩

/-- The forward identification `singleObjXSelf` of the degree `j` term of a single complex is an
`eqToHom`. -/
lemma exists_eqToHom_singleObjXSelf_hom {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}
    [HasZeroMorphisms V] [HasZeroObject V] (j : ι) (A : V) :
    ∃ h, (HomologicalComplex.singleObjXSelf c j A).hom = eqToHom h :=
  exists_eqToHom_singleObjXIsoOfEq_hom j A j rfl

/-- The inverse identification `singleObjXSelf` of the degree `j` term of a single complex is an
`eqToHom`. -/
lemma exists_eqToHom_singleObjXSelf_inv {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}
    [HasZeroMorphisms V] [HasZeroObject V] (j : ι) (A : V) :
    ∃ h, (HomologicalComplex.singleObjXSelf c j A).inv = eqToHom h :=
  ⟨(HomologicalComplex.single_obj_X_self c j A).symm, rfl⟩

/-- A morphism equal to an `eqToHom` morphism is an `eqToHom` morphism. -/
lemma exists_eqToHom_of_eq {a b : V} {f g : a ⟶ b} (e : f = g) (h : ∃ h, g = eqToHom h) :
    ∃ h, f = eqToHom h := e ▸ h

/-- Two parallel `eqToHom` morphisms are equal. -/
lemma eq_of_exists_eqToHom {a b : V} {f g : a ⟶ b} (hf : ∃ h, f = eqToHom h)
    (hg : ∃ h, g = eqToHom h) : f = g := by
  obtain ⟨_, rfl⟩ := hf
  obtain ⟨_, rfl⟩ := hg
  rfl

end Sandwich

/-- The degree-`k` component of `gradedPieceShiftIso` is an identification of objects. -/
lemma gradedPieceShiftIso_hom_f (k : ℕ) :
    ∃ h, (gradedPieceShiftIso B D k).hom.f (k : ℤ) = eqToHom h := by
  simp only [gradedPieceShiftIso, Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, CochainComplex.shiftFunctor_map_f']
  rw [singleFunctors_shiftIso_inv_app_f _ _ _ _ _ _
    ((HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (k : ℤ) _).trans (by
      change _ = ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((deRhamComplex B D).X k)).X ((k : ℤ) + -(k : ℤ))
      rw [add_neg_cancel]
      exact (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) 0 _).symm))]
  · simp only [HomologicalComplex.extendSingleIso, HomologicalComplex.mkHomFromSingle,
      HomologicalComplex.mkHomToSingle_f, dite_eq_left (show (k : ℤ) + -(k : ℤ) = 0 by omega),
      HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso, HomologicalComplex.XIsoOfEq, eqToIso.hom, eqToIso.inv,
      Category.assoc]
    repeat (first | exact ⟨_, rfl⟩ | apply exists_eqToHom_comp)
  · omega

/-- **The multiplications of the graded pieces and of the sheaves of forms in degree zero agree
through the shifts.** The multiplication `Tot(Ω^a[-a] ⊗ Ω^b[-b]) ⟶ Ω^{a + b}[-(a + b)]`, extended
by zero, is the multiplication of `Ω^a[0]` and `Ω^b[0]` read through the identifications
`gradedPieceShiftIso` and the commutations of the total tensor complex with the shift in each
variable. -/
theorem multiplicationInt_gradedPieceWedge_shift (a b : ℕ) :
    multiplicationInt (gradedPieceWedge B D a b) ≫ (gradedPieceShiftIso B D (a + b)).hom =
      HomologicalComplex.mapBifunctorMap (gradedPieceShiftIso B D a).hom
          (gradedPieceShiftIso B D b).hom (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₁Iso ((hodgeSingle B D a).extend embeddingUpNat)
          (((hodgeSingle B D b).extend embeddingUpNat)⟦-(b : ℤ)⟧)
          (sheafTensor.{u, u, u, u, u} A) (-(a : ℤ))).hom ≫
        (CochainComplex.mapBifunctorShift₂Iso ((hodgeSingle B D a).extend embeddingUpNat)
          ((hodgeSingle B D b).extend embeddingUpNat)
          (sheafTensor.{u, u, u, u, u} A) (-(b : ℤ))).hom⟦-(a : ℤ)⟧' ≫
        ((multiplicationInt (hodgeSingleWedge B D a b))⟦-(b : ℤ)⟧')⟦-(a : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (-(b : ℤ)) (-(a : ℤ)) (-((a + b : ℕ) : ℤ)) (by push_cast; ring)).inv.app
          ((hodgeSingle B D (a + b)).extend embeddingUpNat) := by
  ext d : 1
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  by_cases hp : p = (a : ℤ)
  swap
  · exact (isZero_tensorFunctor_obj_obj_of_left (isZero_gradedPiece_extend_X B D a p hp)
      _).eq_of_src _ _
  by_cases hq : q = (b : ℤ)
  swap
  · exact (isZero_tensorFunctor_obj_obj_of_right _
      (isZero_gradedPiece_extend_X B D b q hq)).eq_of_src _ _
  subst hp hq
  obtain rfl : d = ((a + b : ℕ) : ℤ) := by
    have : (a : ℤ) + (b : ℤ) = d := hpq
    push_cast
    exact this.symm
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ (-(a : ℤ)) (a : ℤ) (b : ℤ) _ _
      ((0 : ℕ) : ℤ) (b : ℤ) (by omega) (by push_cast; omega),
    CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctor_map_f',
    CochainComplex.shiftFunctor_map_f']
  simp only [CochainComplex.shiftFunctorObjXIso]
  rw [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ (-(b : ℤ)) ((0 : ℕ) : ℤ)
      (b : ℤ) (b : ℤ)
      _ ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) (by omega) (by omega)]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso.hom,
    eqToIso.inv]
  rw [show (((0 : ℕ) : ℤ) * -(b : ℤ)).negOnePow = 1 by simp, one_smul, Category.assoc,
    Category.assoc, eqToHom_trans_assoc,
    eqToHom_comp_f_eq_assoc (multiplicationInt (hodgeSingleWedge B D a b)) ((0 : ℕ) : ℤ) _
      (by push_cast; omega),
    CochainComplex.shiftFunctorAdd'_inv_app_f']
  simp only [CochainComplex.ιMapBifunctor, eqToHom_refl, Category.id_comp]
  rw [ι_multiplicationInt_f_assoc _ 0 0 0 (by simp),
    ι_multiplicationInt_f_assoc _ (a + b) a b hpq, gradedPieceWedge_f]
  rw [(gradedPieceShiftIso_hom_f B D a).choose_spec, (gradedPieceShiftIso_hom_f B D b).choose_spec,
    (gradedPieceShiftIso_hom_f B D (a + b)).choose_spec]
  simp only [HomologicalComplex.extendXIso,
    HomologicalComplex.extend.XIso, HomologicalComplex.XIsoOfEq, eqToIso.hom, eqToIso.inv,
    eqToHom_map, eqToHom_app, eqToHom_trans, eqToHom_trans_assoc]
  have hL := ι_gradedPieceWedgeDesc B D a b a b (by dsimp)
  rw [gradedPieceWedgeSummand_self] at hL
  have hR := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := hodgeSingle B D a) (K₂ := hodgeSingle B D b) (F := sheafTensor.{u, u, u, u, u} A)
    (c := ComplexShape.up ℕ) (f := fun a' b' h => hodgeSingleWedgeSummand B D a b a' b' h) 0 0 rfl
  refine IsEqToHomSandwich.eq (f := exteriorProductComponent B a b) ?_ ?_
  · refine IsEqToHomSandwich.pre (exists_eqToHom_app (exists_eqToHom_map _ ⟨_, rfl⟩) _) ?_
    refine IsEqToHomSandwich.pre (exists_eqToHom_map _ ⟨_, rfl⟩) ?_
    refine IsEqToHomSandwich.assoc_post ?_ (by exact ⟨_, rfl⟩)
    refine IsEqToHomSandwich.assoc_post ?_ (by exact ⟨_, rfl⟩)
    refine IsEqToHomSandwich.assoc_post ?_ (by exact exists_eqToHom_singleObjXSelf_inv _ _)
    refine IsEqToHomSandwich.of_eq hL ?_
    refine IsEqToHomSandwich.pre (exists_eqToHom_map _ (exists_eqToHom_singleObjXSelf_hom _ _)) ?_
    refine IsEqToHomSandwich.pre (exists_eqToHom_app
      (exists_eqToHom_map _ (exists_eqToHom_singleObjXSelf_hom _ _)) _) ?_
    exact IsEqToHomSandwich.self _
  · refine IsEqToHomSandwich.pre ⟨_, rfl⟩ ?_
    refine IsEqToHomSandwich.pre (exists_eqToHom_app (exists_eqToHom_map _ ⟨_, rfl⟩) _) ?_
    refine IsEqToHomSandwich.pre (exists_eqToHom_map _ ⟨_, rfl⟩) ?_
    refine IsEqToHomSandwich.assoc_post ?_ (by exact ⟨_, rfl⟩)
    refine IsEqToHomSandwich.assoc_post ?_ (by exact ⟨_, rfl⟩)
    refine IsEqToHomSandwich.of_eq (congrArg (_ ≫ ·) (HomologicalComplex.mkHomToSingle_f _ _)) ?_
    refine IsEqToHomSandwich.assoc_post ?_ (exists_eqToHom_singleObjXSelf_inv _ _)
    refine IsEqToHomSandwich.of_eq hR ?_
    unfold hodgeSingleWedgeSummand
    refine IsEqToHomSandwich.pre
      (exists_eqToHom_map _ (exists_eqToHom_singleObjXIsoOfEq_hom _ _ _ _)) ?_
    refine IsEqToHomSandwich.pre (exists_eqToHom_app
      (exists_eqToHom_map _ (exists_eqToHom_singleObjXIsoOfEq_hom _ _ _ _)) _) ?_
    exact IsEqToHomSandwich.self _

end AlgebraicGeometry.SheafOfModules

end
