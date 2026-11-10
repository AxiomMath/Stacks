module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEResolutionTower
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.KInjectiveTowerCocone
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MonoHomologyProjection
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProductsFunctor
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# The essential image of the derived functor of a fully faithful exact functor

Let `F : C ⥤ D` be an exact, fully faithful functor of abelian categories and let `P` be a
property of objects of `C`, closed under isomorphisms and containing zero. Suppose that every
complex `K` of `C` whose cohomology lies in `P` has a K-injective resolution `K ⟶ I` with
`F I` again K-injective. Then the derived functor `F : D(C) ⥤ D(D)` is bijective on `Hom(A, B)`
whenever the cohomology of `B` lies in `P`. This file determines its essential image: an object
`K` of `D(D)` all of whose cohomology objects are of the form `F M` with `P M` is `F B` for some
`B ∈ D_P(C)`.

* For bounded `K` this holds with no further hypothesis.
* For bounded below `K` it holds when countable direct sums are exact in `C` and `D` and preserved
  by `F`.
* For arbitrary `K` it holds when moreover `F` preserves countable products and the cohomology of
  a derived limit of a tower in `D_P(C)` is that of the tower from where the tower is constant (as
  Stacks 0D3E (1) gives on a site).

## Main results

* `CategoryTheory.Functor.bijective_mapDerivedCategory_map_of_exists_isKInjective`: bijectivity
  on `Hom(A, B)` for `B ∈ D_P(C)`.
* `CategoryTheory.Functor.derivedCategoryB_of_mapDerivedCategory_obj_iso`: an object carried to
  one with cohomology in the image of `P` has cohomology in `P`.
* `CategoryTheory.Functor.mem_essImage_mapDerivedCategory_of_isGE_of_isLE`: the bounded case.
* `CategoryTheory.Functor.mem_essImage_mapDerivedCategory_of_isGE`: the bounded below case.
* `CategoryTheory.Functor.mem_essImage_mapDerivedCategory_of_exists_isKInjective`: the general
  case.
* `DerivedCategory.isIso_homologyFunctor_map_comp_π_of_isLimit`: the cohomology of a derived
  limit does not depend on the defining triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategoryB

universe w v u wC vC uC wD vD uD

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The cohomology of a derived limit is that of the tower from where the tower is constant,
whatever defining triangle is used.** Let `L` be a derived limit of a tower `G` for two defining
triangles, with structure maps `p` and `p'`, and suppose `Hᵠ(L)` is the limit of `Hᵠ(Gₙ)` along the
maps `Hᵠ(p' ≫ πₙ)`. If the transition maps `Hᵠ(Gₙ₊₁) ⟶ Hᵠ(Gₙ)` are invertible for `n ≥ N`, then so
is `Hᵠ(p ≫ π_N)`. -/
theorem isIso_homologyFunctor_map_comp_π_of_isLimit (G : ℕᵒᵖ ⥤ DerivedCategory A)
    [HasProduct fun n : ℕ ↦ G.obj ⟨n⟩] {L : DerivedCategory A}
    (p p' : L ⟶ ∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩)
    (δ δ' : (∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang _)
    (hT' : Triangle.mk p' (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) δ' ∈
        distTriang _)
    (q : ℤ) (τ : (Functor.const ℕᵒᵖ).obj ((homologyFunctor A q).obj L) ⟶
      G ⋙ homologyFunctor A q)
    (hτ : ∀ n : ℕ, τ.app ⟨n⟩ = (homologyFunctor A q).map (p' ≫ Pi.π _ n))
    (hlim : IsLimit (Cone.mk _ τ)) (N : ℕ)
    (htrans : ∀ n : ℕ, N ≤ n →
      IsIso ((homologyFunctor A q).map (G.map (homOfLE (Nat.le_succ n)).op))) :
    IsIso ((homologyFunctor A q).map (p ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) N)) := by
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hT hT' (𝟙 _) (𝟙 _)
    (by simp)
  let φ : Triangle.mk p _ δ ⟶ Triangle.mk p' _ δ' :=
    { hom₁ := a
      hom₂ := 𝟙 _
      hom₃ := 𝟙 _
      comm₁ := ha₁
      comm₂ := by simp
      comm₃ := ha₃ }
  have : IsIso a := isIso₁_of_isIso₂₃ φ hT hT' (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  have hc : (G ⋙ homologyFunctor A q).IsEventuallyConstantTo (Opposite.op N) := fun i f ↦ by
    convert isIso_map_to_of_successive_isIso (G ⋙ homologyFunctor A q) N htrans i.unop
      (leOfHom f.unop) using 1
    exact congrArg _ (Subsingleton.elim _ _)
  have : IsIso ((homologyFunctor A q).map (p' ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) N)) := by
    rw [← hτ]
    exact hc.isIso_π_of_isLimit hlim
  rw [show p = a ≫ p' by simpa using ha₁, Category.assoc, Functor.map_comp]
  infer_instance

end DerivedCategory

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Full] [F.Faithful]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

/-- An object with cohomology in `R` is isomorphic to a complex with `S`, given resolutions. -/
private theorem exists_iso_of_derivedCategoryB {R : ObjectProperty C} [R.IsClosedUnderIsomorphisms]
    {S : CochainComplex C ℤ → Prop}
    (hres : ∀ K : CochainComplex C ℤ, derivedCategoryB R (DerivedCategory.Q.obj K) →
      ∃ (I : CochainComplex C ℤ) (γ : K ⟶ I), QuasiIso γ ∧ S I)
    (K : DerivedCategory C) (hK : derivedCategoryB R K) :
    ∃ (I : CochainComplex C ℤ) (_ : DerivedCategory.Q.obj I ≅ K), S I := by
  let eK : DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K) ≅ K :=
    DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨I, γ, hγ, hI⟩ := hres _ fun q ↦
    R.prop_of_iso ((DerivedCategory.homologyFunctor C q).mapIso eK.symm) (hK q)
  exact ⟨I, (asIso (DerivedCategory.Q.map γ)).symm ≪≫ eK, hI⟩

omit [P.ContainsZero] in
/-- **The derived functor of a fully faithful exact functor is bijective on morphisms into
`D_P`**, when every complex with cohomology in `P` has a K-injective resolution which `F` carries
to a K-injective complex. -/
theorem bijective_mapDerivedCategory_map_of_exists_isKInjective
    (hres : ∀ K : CochainComplex C ℤ, derivedCategoryB P (DerivedCategory.Q.obj K) →
      ∃ (I : CochainComplex C ℤ) (γ : K ⟶ I), QuasiIso γ ∧ I.IsKInjective ∧
        CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I))
    (A K : DerivedCategory C) (hK : derivedCategoryB P K) :
    Function.Bijective (F.mapDerivedCategory.map : (A ⟶ K) → _) := by
  obtain ⟨I, e, hI, hFI⟩ := exists_iso_of_derivedCategoryB hres K hK
  exact F.mapDerivedCategory.bijective_map_of_iso (Iso.refl A) e
    (Stacks.KInjectiveTower.bijective_mapDerivedCategory_map_Q_of_isKInjective F A I)

omit [P.ContainsZero] in
/-- **An object carried to one with cohomology in the image of `P` has cohomology in `P`.** -/
theorem derivedCategoryB_of_mapDerivedCategory_obj_iso {B : DerivedCategory C}
    {K : DerivedCategory D} (e : F.mapDerivedCategory.obj B ≅ K)
    (hK : derivedCategoryB (P.map F) K) : derivedCategoryB P B := fun q ↦ by
  obtain ⟨M, hM, ⟨eM⟩⟩ := hK q
  have e' : F.obj ((DerivedCategory.homologyFunctor C q).obj B) ≅ F.obj M :=
    ((F.mapDerivedCategoryHomologyFunctorIso q).app B).symm ≪≫
      (DerivedCategory.homologyFunctor D q).mapIso e ≪≫ eM.symm
  exact P.prop_of_iso (F.preimageIso e').symm hM

open ZeroObject in
omit [F.Full] [F.Faithful] [HasDerivedCategory C] [HasDerivedCategory D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
/-- A zero object lies in the essential image of `P`. -/
theorem map_prop_of_isZero {Y : D} (hY : IsZero Y) : P.map F Y :=
  ⟨0, P.prop_of_isZero (isZero_zero C), ⟨(F.map_isZero (isZero_zero C)).iso hY⟩⟩

omit [P.ContainsZero] in
/-- `D_P` is stable under shifts. -/
theorem derivedCategoryB_shift {B : DerivedCategory C} (hB : derivedCategoryB P B) (a : ℤ) :
    derivedCategoryB P (B⟦a⟧) := fun n ↦
  P.prop_of_iso (((DerivedCategory.homologyFunctor C 0).shiftIso a n (a + n) rfl).app B).symm
    (hB (a + n))

omit [F.Full] [F.Faithful] [HasDerivedCategory C] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
/-- The cohomology of `τ_{< c} K` lies in the image of `P` when that of `K` does. -/
theorem derivedCategoryB_map_truncLT {K : DerivedCategory D}
    (hK : derivedCategoryB (P.map F) K) (c : ℤ) :
    derivedCategoryB (P.map F) ((DerivedCategory.TStructure.t.truncLT c).obj K) := fun i ↦ by
  by_cases hi : i < c
  · exact (P.map F).prop_of_iso
      ((DerivedCategory.truncLTCompHomologyFunctorIso c i hi).app K).symm (hK i)
  · exact map_prop_of_isZero F P
      (DerivedCategory.isZero_of_isLE ((DerivedCategory.TStructure.t.truncLT c).obj K) (c - 1)
        i (by omega))

omit [F.Full] [F.Faithful] [HasDerivedCategory C] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
/-- The cohomology of `τ_{≥ c} K` lies in the image of `P` when that of `K` does. -/
theorem derivedCategoryB_map_truncGE {K : DerivedCategory D}
    (hK : derivedCategoryB (P.map F) K) (c : ℤ) :
    derivedCategoryB (P.map F) ((DerivedCategory.TStructure.t.truncGE c).obj K) := fun i ↦ by
  by_cases hi : c ≤ i
  · exact (P.map F).prop_of_iso
      ((DerivedCategory.truncGECompHomologyFunctorIso c i hi).app K) (hK i)
  · exact map_prop_of_isZero F P
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.TStructure.t.truncGE c).obj K) c
        i (by omega))

omit [F.Full] [F.Faithful] [P.ContainsZero] in
/-- **The essential image is closed under extensions with first term in `D_P`**: in a
distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` of `D(D)` with `X₁ = F B₁`, `B₁ ∈ D_P(C)`, and
`X₃ = F B₃`, the object `X₂` is in the essential image of `F`. -/
theorem mem_essImage_mapDerivedCategory_of_distinguished
    (hbij : ∀ A K : DerivedCategory C, derivedCategoryB P K →
      Function.Bijective (F.mapDerivedCategory.map : (A ⟶ K) → _))
    (T : Triangle (DerivedCategory D)) (hT : T ∈ distTriang _) {B₁ B₃ : DerivedCategory C}
    (e₁ : F.mapDerivedCategory.obj B₁ ≅ T.obj₁) (e₃ : F.mapDerivedCategory.obj B₃ ≅ T.obj₃)
    (hB₁ : derivedCategoryB P B₁) : F.mapDerivedCategory.essImage T.obj₂ := by
  obtain ⟨h, hh⟩ := (hbij B₃ (B₁⟦(1 : ℤ)⟧) (derivedCategoryB_shift P hB₁ 1)).2
    (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app B₁)
  obtain ⟨X₂, f, g, H⟩ := distinguished_cocone_triangle₂ h
  have comm : (F.mapDerivedCategory.map h ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app B₁) ≫ e₁.hom⟦(1 : ℤ)⟧' =
        e₃.hom ≫ T.mor₃ := by
    rw [hh]
    simp [← Functor.map_comp]
  exact ⟨X₂, ⟨Triangle.π₂.mapIso
    (isoTriangleOfIso₁₃ _ _ (F.mapDerivedCategory.map_distinguished _ H) hT e₁ e₃ comm)⟩⟩

omit [F.Full] [F.Faithful] [P.IsClosedUnderIsomorphisms] [P.ContainsZero] in
/-- **An object of `D(D)` concentrated in one degree, with cohomology `F M`, is in the essential
image.** -/
theorem mem_essImage_mapDerivedCategory_of_isGE_of_isLE_self (a : ℤ) (K : DerivedCategory D)
    [K.IsGE a] [K.IsLE a] (hK : derivedCategoryB (P.map F) K) :
    F.mapDerivedCategory.essImage K := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K a
  obtain ⟨M, -, ⟨eM⟩⟩ := hK a
  have eY : F.obj M ≅ Y := eM ≪≫ (DerivedCategory.homologyFunctor D a).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D a).app Y
  exact ⟨(DerivedCategory.singleFunctor C a).obj M,
    ⟨(F.mapDerivedCategorySingleFunctor a).app M ≪≫
      (DerivedCategory.singleFunctor D a).mapIso eY ≪≫ e.symm⟩⟩

/-- **The bounded case**: an object of `D(D)` with cohomology in degrees `[a, a + n]`, each
cohomology object of the form `F M` with `P M`, is in the essential image of `F`. -/
theorem mem_essImage_mapDerivedCategory_of_isGE_of_isLE
    (hbij : ∀ A K : DerivedCategory C, derivedCategoryB P K →
      Function.Bijective (F.mapDerivedCategory.map : (A ⟶ K) → _)) (n : ℕ) :
    ∀ (a : ℤ) (K : DerivedCategory D), K.IsGE a → K.IsLE (a + n) →
      derivedCategoryB (P.map F) K → F.mapDerivedCategory.essImage K := by
  induction n with
  | zero =>
    intro a K hge hle hK
    have : K.IsLE a := by simpa using hle
    exact mem_essImage_mapDerivedCategory_of_isGE_of_isLE_self F P a K hK
  | succ n ih =>
    intro a K hge hle hK
    have hle' : K.IsLE (a + n + 1) := by
      rwa [show a + ((n + 1 : ℕ) : ℤ) = a + n + 1 by push_cast; ring] at hle
    let T := (DerivedCategory.TStructure.t.triangleLTGE (a + n + 1)).obj K
    have hT : T ∈ distTriang _ :=
      DerivedCategory.TStructure.t.triangleLTGE_distinguished (a + n + 1) K
    have h₁ : T.obj₁.IsLE (a + n) :=
      DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _ (by omega)
    have h₁' : T.obj₁.IsGE a := by
      change ((DerivedCategory.TStructure.t.truncLT (a + n + 1)).obj K).IsGE a
      infer_instance
    have h₃ : T.obj₃.IsGE (a + n + 1) := by
      change ((DerivedCategory.TStructure.t.truncGE (a + n + 1)).obj K).IsGE (a + n + 1)
      infer_instance
    have h₃' : T.obj₃.IsLE (a + n + 1) := by
      change ((DerivedCategory.TStructure.t.truncGE (a + n + 1)).obj K).IsLE (a + n + 1)
      infer_instance
    obtain ⟨B₁, ⟨e₁⟩⟩ := ih a T.obj₁ h₁' h₁ (derivedCategoryB_map_truncLT F P hK _)
    obtain ⟨B₃, ⟨e₃⟩⟩ := mem_essImage_mapDerivedCategory_of_isGE_of_isLE_self F P (a + n + 1)
      T.obj₃ (derivedCategoryB_map_truncGE F P hK _)
    exact mem_essImage_mapDerivedCategory_of_distinguished F P hbij T hT e₁ e₃
      (derivedCategoryB_of_mapDerivedCategory_obj_iso F P e₁
        (derivedCategoryB_map_truncLT F P hK _))

section BoundedBelow

variable [PreservesColimitsOfShape (Discrete ℕ) F]

/-- **The bounded below case**: when countable direct sums are exact in `C` and `D` and `F`
preserves them, an object of `D(D)` bounded below whose cohomology objects are of the form `F M`
with `P M` is in the essential image of `F`. -/
theorem mem_essImage_mapDerivedCategory_of_isGE
    (hbij : ∀ A K : DerivedCategory C, derivedCategoryB P K →
      Function.Bijective (F.mapDerivedCategory.map : (A ⟶ K) → _))
    (hC : HasExactCountableDirectSums C) (hD : HasExactCountableDirectSums D)
    [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
    (a : ℤ) (K : DerivedCategory D) [K.IsGE a] (hK : derivedCategoryB (P.map F) K) :
    F.mapDerivedCategory.essImage K := by
  let X : ℕ → DerivedCategory D := fun m ↦
    (DerivedCategory.TStructure.t.truncLT (a + m + 1)).obj K
  have hX (m : ℕ) : F.mapDerivedCategory.essImage (X m) := by
    have : (X m).IsLE (a + m) := DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _ (by omega)
    have : (X m).IsGE a := by
      change ((DerivedCategory.TStructure.t.truncLT (a + m + 1)).obj K).IsGE a
      infer_instance
    exact mem_essImage_mapDerivedCategory_of_isGE_of_isLE F P hbij m a (X m) ‹_› ‹_›
      (derivedCategoryB_map_truncLT F P hK _)
  choose B hB using hX
  let e : ∀ m, F.mapDerivedCategory.obj (B m) ≅ X m := fun m ↦ (hB m).some
  have hBP (m : ℕ) : derivedCategoryB P (B m) :=
    derivedCategoryB_of_mapDerivedCategory_obj_iso F P (e m)
      (derivedCategoryB_map_truncLT F P hK _)
  let τ : ∀ m, X m ⟶ X (m + 1) := fun m ↦
    (DerivedCategory.TStructure.t.natTransTruncLTOfLE _ _ (by push_cast; omega)).app K
  have hτ (m : ℕ) : τ m ≫ (DerivedCategory.TStructure.t.truncLTι _).app K =
      (DerivedCategory.TStructure.t.truncLTι _).app K :=
    DerivedCategory.TStructure.t.natTransTruncLTOfLE_ι_app _ _ _ K
  have hβ (m : ℕ) := (hbij (B m) (B (m + 1)) (hBP (m + 1))).2
    ((e m).hom ≫ τ m ≫ (e (m + 1)).inv)
  choose β hβ using hβ
  let G : ℕ ⥤ DerivedCategory C := Functor.ofSequence β
  have hG (m : ℕ) : G.map (homOfLE (Nat.le_succ m)) = β m :=
    Functor.ofSequence_map_homOfLE_succ β m
  let ℓ : ∀ m, F.mapDerivedCategory.obj (B m) ⟶ K := fun m ↦
    (e m).hom ≫ (DerivedCategory.TStructure.t.truncLTι _).app K
  have hℓβ (m : ℕ) : F.mapDerivedCategory.map (β m) ≫ ℓ (m + 1) = ℓ m := by
    rw [hβ]
    simp only [ℓ, Category.assoc, Iso.inv_hom_id_assoc, hτ]
  have hℓ (m : ℕ) :
      F.mapDerivedCategory.map (G.map (homOfLE (Nat.le_succ m))) ≫ ℓ (m + 1) = ℓ m :=
    (congrArg (fun φ ↦ F.mapDerivedCategory.map φ ≫ ℓ (m + 1)) (hG m)).trans (hℓβ m)
  have : HasCountableCoproducts (DerivedCategory C) := derivedCategory_hasCountableCoproducts C hC
  have : HasCountableCoproducts (DerivedCategory D) := derivedCategory_hasCountableCoproducts D hD
  have := mapDerivedCategory_preservesCountableCoproducts hC hD F
  obtain ⟨L, p, q, hT⟩ := distinguished_cocone_triangle (Limits.Sigma.desc fun n ↦
    Limits.Sigma.ι G.obj n - G.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι G.obj (n + 1))
  have hL : IsHomotopyColimitWith G L (fun n ↦ Limits.Sigma.ι G.obj n ≫ p) :=
    ⟨p, q, hT, fun _ ↦ rfl⟩
  obtain ⟨p', q', hT', -⟩ := hL.map F.mapDerivedCategory
  let g : ∐ (G ⋙ F.mapDerivedCategory).obj ⟶ K := Limits.Sigma.desc ℓ
  have hι (n : ℕ) : Limits.Sigma.ι (G ⋙ F.mapDerivedCategory).obj n ≫ Limits.Sigma.desc ℓ =
      ℓ n :=
    Limits.Sigma.ι_comp_desc ℓ n
  have hg : (Limits.Sigma.desc fun n ↦ Limits.Sigma.ι (G ⋙ F.mapDerivedCategory).obj n -
      (G ⋙ F.mapDerivedCategory).map (homOfLE (Nat.le_succ n)) ≫
        Limits.Sigma.ι (G ⋙ F.mapDerivedCategory).obj (n + 1)) ≫ g = 0 := by
    refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_
    simp only [g, Limits.Sigma.ι_comp_desc_assoc, Preadditive.sub_comp, Category.assoc,
      Functor.comp_map, comp_zero]
    rw [hι, hι, hℓ]
    exact sub_self _
  obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ hT' g hg
  have hσ (n : ℕ) : Limits.Sigma.ι (G ⋙ F.mapDerivedCategory).obj n ≫ p' ≫ h = ℓ n := by
    have hh' : p' ≫ h = g := hh.symm
    rw [hh']
    exact hι n
  have : IsIso h := by
    rw [DerivedCategory.isIso_iff]
    intro r
    let H := DerivedCategory.homologyFunctor D r
    have : PreservesColimitsOfShape (Discrete ℕ) H := by
      have : HasCoproductsOfShape ℕ D := hD.hasCoproducts.1 ℕ
      have := derivedCategory_Q_preservesCoproductsOfShape D hD ℕ
      have := homologicalComplex_homologyFunctor_preservesCoproducts D hD ℕ r
      have : PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.Q ⋙ H) :=
        preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors D r).symm
      exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q H ℕ
    obtain ⟨eH, heH⟩ := exists_iso_colimit_of_isHomotopyColimit
      (G ⋙ F.mapDerivedCategory) H p' q' hT'
    let m₀ : ℕ := (r - a).toNat
    have hℓiso (m : ℕ) (hm : m₀ ≤ m) : IsIso (H.map (ℓ m)) := by
      have := DerivedCategory.isIso_homologyMap_truncLTι_app (a + m + 1) r (by omega) K
      rw [Functor.map_comp]
      infer_instance
    let c₀ : Cocone ((G ⋙ F.mapDerivedCategory) ⋙ H) :=
      { pt := H.obj K
        ι := NatTrans.ofSequence (fun m ↦ H.map (ℓ m)) fun m ↦ by
          simp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map,
            Category.comp_id]
          exact (H.map_comp _ _).symm.trans (congrArg H.map (hℓ m)) }
    have hconst : ((G ⋙ F.mapDerivedCategory) ⋙ H).IsEventuallyConstantFrom m₀ :=
      fun j f ↦ by
        have : IsIso (c₀.ι.app j) := hℓiso j (leOfHom f)
        have : IsIso (c₀.ι.app m₀) := hℓiso m₀ le_rfl
        exact IsIso.of_isIso_fac_right (c₀.w f)
    have : IsIso (c₀.ι.app m₀) := hℓiso m₀ le_rfl
    let hcol := hconst.isColimitOfIsIso c₀
    let e₀ := (colimit.isColimit _).coconePointUniqueUpToIso hcol
    have he₀ (n : ℕ) : colimit.ι _ n ≫ e₀.hom = c₀.ι.app n :=
      IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
    have heq : eH.hom ≫ H.map h = e₀.hom := colimit.hom_ext fun n ↦
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ H.map h) (heH n)).trans
        ((H.map_comp _ _).symm.trans ((congrArg H.map ((Category.assoc _ _ _).trans
          (hσ n))).trans (he₀ n).symm)))
    have : H.map h = eH.inv ≫ e₀.hom := by rw [← heq, Iso.inv_hom_id_assoc]
    change IsIso (H.map h)
    rw [this]
    infer_instance
  exact ⟨L, ⟨asIso h⟩⟩

end BoundedBelow

section Unbounded

variable [HasProductsOfShape ℕ C] [HasProductsOfShape ℕ D]
  [HasProductsOfShape ℕ (DerivedCategory C)] [HasProductsOfShape ℕ (DerivedCategory D)]
  [PreservesLimitsOfShape (Discrete ℕ) F]

omit [F.Full] [F.Faithful] in
/-- **The derived functor preserves a countable product of K-injective complexes which `F`
carries to K-injective complexes.** -/
theorem isIso_piComparison_mapDerivedCategory_Q_of_isKInjective (I : ℕ → CochainComplex C ℤ)
    (hI : ∀ n, (I n).IsKInjective)
    (hFI : ∀ n, CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj (I n))) :
    IsIso (piComparison F.mapDerivedCategory fun n ↦ DerivedCategory.Q.obj (I n)) := by
  have hcomplex : IsIso (piComparison
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) I) := by
    rw [Stacks.DerivedProducts.piComparison_comp_eq]
    have h₁ : IsIso (piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ)) I) :=
      inferInstance
    have h₂ : IsIso (piComparison DerivedCategory.Q
        fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I n)) :=
      Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective _ hFI
    infer_instance
  have : PreservesLimit (Discrete.functor I)
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :=
    have := hcomplex
    PreservesProduct.of_iso_comparison _ I
  have : PreservesLimit (Discrete.functor I) (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimit_of_natIso _ F.mapDerivedCategoryFactors.symm
  have hcomp : IsIso (piComparison (DerivedCategory.Q ⋙ F.mapDerivedCategory) I) :=
    inferInstance
  rw [Stacks.DerivedProducts.piComparison_comp_eq] at hcomp
  have hQ : IsIso (piComparison (DerivedCategory.Q (C := C)) I) :=
    Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective I hI
  have : IsIso (F.mapDerivedCategory.map (piComparison (DerivedCategory.Q (C := C)) I)) :=
    inferInstance
  exact IsIso.of_isIso_comp_left
    (F.mapDerivedCategory.map (piComparison (DerivedCategory.Q (C := C)) I)) _

variable [PreservesColimitsOfShape (Discrete ℕ) F]

/-- **The essential image of the derived functor of a fully faithful exact functor.** Let `F`
be exact, fully faithful, preserving countable products and direct sums, with countable direct
sums exact in `C` and `D`, and suppose every complex with cohomology in `P` has a K-injective
resolution carried by `F` to a K-injective complex. Suppose also that in `D(C)` the derived limit
of a tower of objects of `D_P` with surjective transition maps on cohomology has, in each degree,
the cohomology of the tower from the index on which the tower is constant (as Stacks 0D3E (1)
gives on a site). Then every object of `D(D)` whose cohomology objects are of the form `F M`
with `P M` is `F B` for some `B`. -/
theorem mem_essImage_mapDerivedCategory_of_exists_isKInjective
    (hres : ∀ K : CochainComplex C ℤ, derivedCategoryB P (DerivedCategory.Q.obj K) →
      ∃ (I : CochainComplex C ℤ) (γ : K ⟶ I), QuasiIso γ ∧ I.IsKInjective ∧
        CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I))
    (hlim : ∀ G : ℕᵒᵖ ⥤ DerivedCategory C, (∀ n : ℕ, derivedCategoryB P (G.obj ⟨n⟩)) →
      (∀ (n : ℕ) (q : ℤ), Epi ((DerivedCategory.homologyFunctor C q).map
        (G.map (homOfLE (Nat.le_succ n)).op))) →
      ∀ (L : DerivedCategory C) (p : L ⟶ ∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩)
        (δ : (∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧),
        Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang _ →
      ∀ (q : ℤ) (N : ℕ), (∀ n : ℕ, N ≤ n → IsIso ((DerivedCategory.homologyFunctor C q).map
        (G.map (homOfLE (Nat.le_succ n)).op))) →
        IsIso ((DerivedCategory.homologyFunctor C q).map
          (p ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) N)))
    (hC : HasExactCountableDirectSums C) (hD : HasExactCountableDirectSums D)
    [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
    (K : DerivedCategory D) (hK : derivedCategoryB (P.map F) K) :
    F.mapDerivedCategory.essImage K := by
  have hbij := bijective_mapDerivedCategory_map_of_exists_isKInjective F P hres
  let X : ℕ → DerivedCategory D := fun n ↦
    (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K
  have hX (n : ℕ) : F.mapDerivedCategory.essImage (X n) := by
    have : (X n).IsGE (-(n : ℤ)) := by
      change ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K).IsGE (-(n : ℤ))
      infer_instance
    exact mem_essImage_mapDerivedCategory_of_isGE F P hbij hC hD (-(n : ℤ)) (X n)
      (derivedCategoryB_map_truncGE F P hK _)
  choose B hB using hX
  let e : ∀ n, F.mapDerivedCategory.obj (B n) ≅ X n := fun n ↦ (hB n).some
  have hBP (n : ℕ) : derivedCategoryB P (B n) :=
    derivedCategoryB_of_mapDerivedCategory_obj_iso F P (e n)
      (derivedCategoryB_map_truncGE F P hK _)
  let τ : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
    (DerivedCategory.TStructure.t.natTransTruncGEOfLE _ _ (by push_cast; omega)).app K
  have hτ (n : ℕ) : (DerivedCategory.TStructure.t.truncGEπ _).app K ≫ τ n =
      (DerivedCategory.TStructure.t.truncGEπ _).app K :=
    DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app _ _ _ K
  have hτH (n : ℕ) (q : ℤ) : Epi ((DerivedCategory.homologyFunctor D q).map (τ n)) ∧
      (-(n : ℤ) ≤ q → IsIso ((DerivedCategory.homologyFunctor D q).map (τ n))) := by
    have hiso : -(n : ℤ) ≤ q → IsIso ((DerivedCategory.homologyFunctor D q).map (τ n)) :=
      fun hq ↦ by
        have := DerivedCategory.isIso_homologyMap_truncGEπ_app (-((n + 1 : ℕ) : ℤ)) q
          (by push_cast; omega) K
        have := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(n : ℤ)) q hq K
        have h := congrArg (DerivedCategory.homologyFunctor D q).map (hτ n)
        rw [Functor.map_comp] at h
        exact IsIso.of_isIso_fac_left h
    refine ⟨?_, hiso⟩
    by_cases hq : -(n : ℤ) ≤ q
    · have := hiso hq
      infer_instance
    · have : (X n).IsGE (-(n : ℤ)) := by
        change ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K).IsGE (-(n : ℤ))
        infer_instance
      exact (DerivedCategory.isZero_of_isGE (X n) (-(n : ℤ)) q (by omega)).epi _
  have hβ (n : ℕ) := (hbij (B (n + 1)) (B n) (hBP n)).2 ((e (n + 1)).hom ≫ τ n ≫ (e n).inv)
  choose β hβ using hβ
  let G : ℕᵒᵖ ⥤ DerivedCategory C := Functor.ofOpSequence β
  have hβG (n : ℕ) : F.mapDerivedCategory.map (G.map (homOfLE (Nat.le_succ n)).op) =
      (e (n + 1)).hom ≫ τ n ≫ (e n).inv :=
    (congrArg F.mapDerivedCategory.map (Functor.ofOpSequence_map_homOfLE_succ β n)).trans (hβ n)
  have hcomp (n : ℕ) (q : ℤ) :
      Epi ((DerivedCategory.homologyFunctor D q).map ((e (n + 1)).hom ≫ τ n ≫ (e n).inv)) ∧
      (-(n : ℤ) ≤ q →
        IsIso ((DerivedCategory.homologyFunctor D q).map ((e (n + 1)).hom ≫ τ n ≫ (e n).inv))) := by
    rw [Functor.map_comp, Functor.map_comp]
    refine ⟨?_, fun hq ↦ ?_⟩
    · have := (hτH n q).1
      infer_instance
    · have := (hτH n q).2 hq
      infer_instance
  have hGH (n : ℕ) (q : ℤ) : Epi ((DerivedCategory.homologyFunctor C q).map
        (G.map (homOfLE (Nat.le_succ n)).op)) ∧
      (-(n : ℤ) ≤ q → IsIso ((DerivedCategory.homologyFunctor C q).map
        (G.map (homOfLE (Nat.le_succ n)).op))) := by
    refine ⟨(F.epi_map_iff_epi _).1 ?_,
      fun hq ↦ (isIso_iff_of_reflects_iso _ F).1
        ((F.isIso_homologyFunctor_map_mapDerivedCategory_map_iff _ q).1 ?_)⟩
    · have hn := NatIso.naturality_1 (F.mapDerivedCategoryHomologyIso q)
        (G.map (homOfLE (Nat.le_succ n)).op)
      have : Epi ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D q).map
          (G.map (homOfLE (Nat.le_succ n)).op)) := by
        change Epi ((DerivedCategory.homologyFunctor D q).map
          (F.mapDerivedCategory.map (G.map (homOfLE (Nat.le_succ n)).op)))
        rw [hβG]
        exact (hcomp n q).1
      change Epi ((DerivedCategory.homologyFunctor C q ⋙ F).map
        (G.map (homOfLE (Nat.le_succ n)).op))
      rw [← hn]
      infer_instance
    · rw [hβG]
      exact (hcomp n q).2 hq
  let ℓ : ∀ n : ℕ, K ⟶ F.mapDerivedCategory.obj (G.obj ⟨n⟩) := fun n ↦
    (DerivedCategory.TStructure.t.truncGEπ _).app K ≫ (e n).inv
  have hℓB (n : ℕ) : ((DerivedCategory.TStructure.t.truncGEπ _).app K ≫ (e (n + 1)).inv) ≫
      (e (n + 1)).hom ≫ τ n ≫ (e n).inv =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K ≫ (e n).inv := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hτ]
  have hℓ (n : ℕ) :
      ℓ (n + 1) ≫ F.mapDerivedCategory.map (G.map (homOfLE (Nat.le_succ n)).op) = ℓ n :=
    (congrArg (ℓ (n + 1) ≫ ·) (hβG n)).trans (hℓB n)
  obtain ⟨L, p, δ, hT⟩ := exists_isDerivedLimit G
  have : PreservesLimit (Discrete.functor fun n : ℕ ↦ G.obj ⟨n⟩) F.mapDerivedCategory := by
    have hres' (n : ℕ) := exists_iso_of_derivedCategoryB hres (B n) (hBP n)
    choose I e' hI hFI using hres'
    have hi : IsIso (piComparison F.mapDerivedCategory fun n ↦ G.obj ⟨n⟩) :=
      isIso_piComparison_of_iso F.mapDerivedCategory
        e'
        (isIso_piComparison_mapDerivedCategory_Q_of_isKInjective F I hI hFI)
    exact PreservesProduct.of_iso_comparison _ _
  obtain ⟨δ', hT'⟩ :=
    Stacks.Injectives.isDerivedLimit_map_of_preservesProduct F.mapDerivedCategory G L p ⟨δ, hT⟩
  have hf : Pi.lift ℓ ≫ (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.mapDerivedCategory.obj (G.obj ⟨n⟩)) n -
        Pi.π (fun n : ℕ ↦ F.mapDerivedCategory.obj (G.obj ⟨n⟩)) (n + 1) ≫
          F.mapDerivedCategory.map (G.map (homOfLE (Nat.le_succ n)).op)) = 0 := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp only [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, Pi.lift_comp_π_assoc,
      zero_comp]
    rw [hℓ, sub_self]
  obtain ⟨c, hc⟩ := Triangle.coyoneda_exact₂ _ hT' (Pi.lift ℓ) hf
  have hkey (N : ℕ) : c ≫ F.mapDerivedCategory.map (p ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) N) =
      ℓ N := by
    have h := congrArg (· ≫ Pi.π (fun n : ℕ ↦ F.mapDerivedCategory.obj (G.obj ⟨n⟩)) N) hc
    simp only [Pi.lift_comp_π, Triangle.mk_mor₁, Category.assoc, piComparison_comp_π] at h
    rw [h, Functor.map_comp]
  have : IsIso c := by
    rw [DerivedCategory.isIso_iff]
    intro r
    let N : ℕ := (-r).toNat
    have h₁ : IsIso ((DerivedCategory.homologyFunctor D r).map
        (c ≫ F.mapDerivedCategory.map (p ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) N))) := by
      rw [hkey]
      have := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(N : ℤ)) r (by omega) K
      change IsIso ((DerivedCategory.homologyFunctor D r).map
        ((DerivedCategory.TStructure.t.truncGEπ _).app K ≫ (e N).inv))
      rw [Functor.map_comp]
      infer_instance
    have h₂ : IsIso ((DerivedCategory.homologyFunctor D r).map
        (F.mapDerivedCategory.map (p ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) N))) :=
      (F.isIso_homologyFunctor_map_mapDerivedCategory_map_iff _ r).2
        ((isIso_iff_of_reflects_iso _ F).2
          (hlim G hBP (fun n q ↦ (hGH n q).1) L p δ hT r N fun n hn ↦
            (hGH n r).2 (by omega)))
    rw [Functor.map_comp] at h₁
    exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor D r).map
      (F.mapDerivedCategory.map (p ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) N)))
  exact ⟨L, ⟨(asIso c).symm⟩⟩

end Unbounded

end CategoryTheory.Functor

end
