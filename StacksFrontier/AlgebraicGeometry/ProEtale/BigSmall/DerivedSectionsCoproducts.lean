module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.DerivedComparisonBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.AbelianSections
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit

/-!
# Derived sections commute with direct sums and homotopy colimits

Let `U` be an object of a site admitting a hypercovering `K` whose term in each degree is a
*one-element* family on an object which is quasi-compact (Stacks 090H) and over which taking
sections of abelian sheaves is exact (the conclusion of Stacks 0946 at a weakly contractible
object). Then derived sections `RΓ(U, -) : D⁺(Sh(J, Ab)) ⥤ D(Ab)` commute with direct sums and
with homotopy colimits.

## Main definitions

* `IsSingletonExactQuasiCompact` packages the hypotheses on the hypercovering: in each degree it
  is a one-element family on a quasi-compact object with exact sections.

## Main results

* `preservesColimitsOfShape_discrete_derivedSectionsPlus`: `RΓ(U, -)` carries every colimit
  cocone on a family of bounded below objects to a colimit cocone in `D(Ab)`.
* `isColimit_mapCofan_derivedSectionsPlus`: the same statement read off a cofan: if `S` with
  maps `E i ⟶ S` is the direct sum of the family `E`, then `RΓ(U, S)` with the images of those
  maps is the direct sum of the `RΓ(U, E i)`.
* `isHomotopyColimit_derivedSectionsPlus`: `RΓ(U, -)` carries a homotopy colimit of a system of
  bounded below objects to a homotopy colimit.

## References

* [Stacks Project, Tag 09A3](https://stacks.math.columbia.edu/tag/09A3)
* [Stacks Project, Tag 09A1](https://stacks.math.columbia.edu/tag/09A1)
* [Stacks Project, Tag 09A2](https://stacks.math.columbia.edu/tag/09A2)
* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape Simplicial

universe t w v u

namespace Stacks.CategoryTheory.Hypercovering

section CofanHelpers

variable {𝒞 : Type*} [Category* 𝒞] {𝒟 : Type*} [Category* 𝒟]

/-- A colimit cofan on a family of zero objects has zero point. -/
private lemma isZero_cofan_pt_of_isZero {ι : Type*} {A : ι → 𝒞} [HasZeroMorphisms 𝒞] {S : 𝒞}
    (inj : ∀ i, A i ⟶ S) (hc : IsColimit (Cofan.mk S inj)) (h : ∀ i, IsZero (A i)) :
    IsZero S := by
  rw [IsZero.iff_id_eq_zero]
  refine hc.hom_ext ?_
  rintro ⟨i⟩
  show inj i ≫ 𝟙 S = inj i ≫ 0
  rw [(h i).eq_of_src (inj i) 0, Limits.zero_comp, Limits.zero_comp]

/-- Each injection into a coproduct is a split monomorphism: the cofan whose `i`-th leg is the
identity and whose other legs vanish provides the retraction. -/
private lemma exists_retraction_of_isColimit_cofan {ι : Type*} {A : ι → 𝒞} [HasZeroMorphisms 𝒞]
    {S : 𝒞} (inj : ∀ i, A i ⟶ S) (hc : IsColimit (Cofan.mk S inj)) (i : ι) :
    ∃ r : S ⟶ A i, inj i ≫ r = 𝟙 (A i) := by
  classical
  refine ⟨hc.desc (Cofan.mk (A i) (fun j => if h : j = i then eqToHom (congrArg A h) else 0)), ?_⟩
  have h := hc.fac (Cofan.mk (A i) (fun j => if h : j = i then eqToHom (congrArg A h) else 0))
    ⟨i⟩
  simpa using h

/-- Transport a colimit cofan along isomorphisms of the family and of the point. -/
private def isColimit_cofan_congr {ι : Type*} {A A' : ι → 𝒞} (e : ∀ j, A j ≅ A' j)
    {S S' : 𝒞} (inj : ∀ j, A j ⟶ S) (inj' : ∀ j, A' j ⟶ S') (φ : S ≅ S')
    (h : ∀ j, inj j ≫ φ.hom = (e j).hom ≫ inj' j)
    (hc : IsColimit (Cofan.mk S inj)) :
    IsColimit (Cofan.mk S' inj') := by
  have h' : ∀ j, inj' j ≫ φ.inv = (e j).inv ≫ inj j := fun j => by
    rw [Iso.comp_inv_eq, Category.assoc, h j, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hfac : ∀ (s : Cofan A') (j : ι),
      inj j ≫ Cofan.IsColimit.desc hc (fun k => (e k).hom ≫ s.inj k) = (e j).hom ≫ s.inj j :=
    fun s j => Cofan.IsColimit.fac hc _ j
  have hext : ∀ {T : 𝒞} (m₁ m₂ : S ⟶ T), (∀ j, inj j ≫ m₁ = inj j ≫ m₂) → m₁ = m₂ :=
    fun m₁ m₂ hm => Cofan.IsColimit.hom_ext hc m₁ m₂ hm
  refine ⟨fun s => φ.inv ≫ Cofan.IsColimit.desc hc (fun k => (e k).hom ≫ Cofan.inj s k), ?_, ?_⟩
  · rintro s ⟨j⟩
    change inj' j ≫ φ.inv ≫
      Cofan.IsColimit.desc hc (fun k => (e k).hom ≫ Cofan.inj s k) = Cofan.inj s j
    rw [← Category.assoc, h' j, Category.assoc, hfac s j, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  · intro s m hm
    have key : φ.hom ≫ m = Cofan.IsColimit.desc hc (fun k => (e k).hom ≫ Cofan.inj s k) := by
      refine hext _ _ (fun j => ?_)
      rw [← Category.assoc, h j, Category.assoc, hfac s j]
      exact congrArg (fun z => (e j).hom ≫ z) (hm ⟨j⟩)
    rw [← key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A functor preserving the coproduct carries a colimit cofan to a colimit cofan. -/
private def isColimit_cofan_map_of_preserves (F : 𝒞 ⥤ 𝒟) {ι : Type*} {A : ι → 𝒞} {S : 𝒞}
    (inj : ∀ j, A j ⟶ S) [PreservesColimit (Discrete.functor A) F]
    (hc : IsColimit (Cofan.mk S inj)) :
    IsColimit (Cofan.mk (F.obj S) (fun j => F.map (inj j))) :=
  Cofan.isColimitMapCoconeEquiv F A _ (isColimitOfPreserves F hc)

/-- A colimit cofan is carried to a colimit cofan by a functor as soon as it is by an
isomorphic functor. -/
private def isColimit_cofan_map_of_natIso {F G : 𝒞 ⥤ 𝒟} (e : F ≅ G) {ι : Type*} {A : ι → 𝒞}
    {S : 𝒞} (inj : ∀ j, A j ⟶ S)
    (h : IsColimit (Cofan.mk (G.obj S) (fun j => G.map (inj j)))) :
    IsColimit (Cofan.mk (F.obj S) (fun j => F.map (inj j))) :=
  isColimit_cofan_congr (fun j => (e.app (A j)).symm) (fun j => G.map (inj j))
    (fun j => F.map (inj j)) (e.app S).symm (fun j => e.inv.naturality (inj j)) h

/-- A functor carries a colimit cofan to a colimit cofan as soon as it does so for one colimit
cofan on an isomorphic family. -/
private def isColimit_mapCofan_of_isColimit_mapCofan (F : 𝒞 ⥤ 𝒟) {ι : Type*} {A A' : ι → 𝒞}
    (e : ∀ j, A j ≅ A' j) {S : 𝒞} (inj : ∀ j, A j ⟶ S) (hc : IsColimit (Cofan.mk S inj))
    {T : 𝒞} (inj' : ∀ j, A' j ⟶ T) (hd : IsColimit (Cofan.mk T inj'))
    (h : IsColimit (Cofan.mk (F.obj T) (fun j => F.map (inj' j)))) :
    IsColimit (Cofan.mk (F.obj S) (fun j => F.map (inj j))) := by
  have hc' : IsColimit (Cofan.mk S (fun j => (e j).inv ≫ inj j)) :=
    isColimit_cofan_congr e inj _ (Iso.refl S) (fun j => by
      rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]) hc
  have hsq : ∀ j, inj' j ≫ (hd.coconePointUniqueUpToIso hc').hom = (e j).inv ≫ inj j :=
    fun j => hd.comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩
  refine isColimit_cofan_congr (fun j => (F.mapIso (e j)).symm) (fun j => F.map (inj' j))
    (fun j => F.map (inj j)) (F.mapIso (hd.coconePointUniqueUpToIso hc')) (fun j => ?_) h
  change F.map (inj' j) ≫ F.map _ = F.map (e j).inv ≫ F.map (inj j)
  rw [← F.map_comp, ← F.map_comp, hsq j]

/-- Pasting two commuting squares: if `a ≫ b = c ≫ d` and `d ≫ p = q ≫ r`, then
`a ≫ b ≫ p = (c ≫ q) ≫ r`. -/
private lemma comp_assoc_square {A B B' E E' D : 𝒞} (a : A ⟶ B) (b : B ⟶ B') (c : A ⟶ E)
    (d : E ⟶ B') (p : B' ⟶ D) (q : E ⟶ E') (r : E' ⟶ D)
    (h1 : a ≫ b = c ≫ d) (h2 : d ≫ p = q ≫ r) :
    a ≫ b ≫ p = (c ≫ q) ≫ r := by
  rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc]

/-- A functor all of whose values are zero objects preserves all colimits. -/
private lemma preservesColimitsOfShape_of_isZero {J : Type*} [Category* J] (F : 𝒞 ⥤ 𝒟)
    (h : ∀ X, IsZero (F.obj X)) : PreservesColimitsOfShape J F := by
  constructor
  intro D
  constructor
  intro c hc
  exact ⟨{
    desc := fun s => (h c.pt).to_ _
    fac := fun s j => ((h (D.obj j)).eq_of_src _ _)
    uniq := fun s m _ => (h c.pt).eq_of_src _ _ }⟩

end CofanHelpers

attribute [local instance] HasDerivedCategory.standard

section General

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (J : Pretopology C) (U : C)
  (K : SimplicialObject (FormalCoproduct.{w} (Over U)))

section Degreewise

/-- **A one-element hypercovering term computes sections over its single member.** For a degree
in which the hypercovering is a one-element family, evaluating the hypercover cochain complex
there is the functor of sections over that single member, naturally in the abelian sheaf. -/
private def hypercoverDegreeNatIso (n : ℕ) [Unique (K.obj (op ⦋n⦌)).I] :
    hypercoverCochainNatFunctor J U K ⋙
        HomologicalComplex.eval AddCommGrpCat.{max u v w} (up ℕ) n ≅
      sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left := by
  refine NatIso.ofComponents (fun F =>
    SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F ≪≫
      Limits.productUniqueIso _) (fun {F G} g => ?_)
  have hnat : ((hypercoverCochainNatFunctor J U K).map g).f n ≫
      (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) G).hom =
      (SectionsOver.evalOpProductIso J.toGrothendieck (K.obj (op ⦋n⦌)) F).hom ≫
        Limits.Pi.map (fun i ↦ g.hom.app (op ((K.obj (op ⦋n⦌)).obj i).left)) := rfl
  have h2 : Limits.Pi.map (fun i ↦ g.hom.app (op ((K.obj (op ⦋n⦌)).obj i).left)) ≫
        (Limits.productUniqueIso
          (fun i ↦ G.obj.obj (op ((K.obj (op ⦋n⦌)).obj i).left))).hom =
      (Limits.productUniqueIso (fun i ↦ F.obj.obj (op ((K.obj (op ⦋n⦌)).obj i).left))).hom ≫
        g.hom.app (op ((K.obj (op ⦋n⦌)).obj default).left) := by
    rw [Limits.productUniqueIso_hom, Limits.productUniqueIso_hom]
    exact Limits.Pi.map_π _ _
  exact comp_assoc_square _ _ _ _ _ _ _ hnat h2

/-- The same identification in integer degrees: the hypercover cochain complex of an abelian
sheaf, extended by zero to integer degrees, has as its degree-`n` term the sections over the
single member of the degree-`n` term of the hypercovering. -/
private def hypercoverDegreeIntIso (n : ℕ) [Unique (K.obj (op ⦋n⦌)).I] :
    hypercoverCochainIntFunctor J U K ⋙
        HomologicalComplex.eval AddCommGrpCat.{max u v w} (up ℤ) (n : ℤ) ≅
      sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left :=
  Functor.isoWhiskerLeft (hypercoverCochainNatFunctor J U K)
      (embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{max u v w} (i := n) rfl) ≪≫
    hypercoverDegreeNatIso J U K n

/-- In negative degrees the hypercover cochain complex vanishes. -/
private lemma isZero_hypercoverCochainInt_X (p : ℤ) (hp : p < 0)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    IsZero (((hypercoverCochainIntFunctor J U K).obj F).X p) :=
  CochainComplex.isZero_of_isStrictlyGE
    (((hypercoverCochainNatFunctor J U K).obj F).extend embeddingUpNat) 0 p hp

/-- **Degreewise exactness.** If sections over the single member of each term of the
hypercovering are exact, then so is evaluation of the hypercover cochain complex in each integer
degree. -/
private lemma exactFunctor_hypercoverCochainInt_comp_eval
    [∀ n : ℕ, Unique (K.obj (op ⦋n⦌)).I]
    (hexact : ∀ n : ℕ, exactFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max u v w} (sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left))
    (n : ℕ) :
    exactFunctor _ _ (hypercoverCochainIntFunctor J U K ⋙
      HomologicalComplex.eval AddCommGrpCat.{max u v w} (up ℤ) (n : ℤ)) :=
  ObjectProperty.prop_of_iso _ (hypercoverDegreeIntIso J U K n).symm (hexact n)

/-- **Degreewise preservation of direct sums.** If the single member of each term of the
hypercovering is a quasi-compact object of the site, then the hypercover cochain complex of an
abelian sheaf commutes with direct sums. -/
private lemma preservesColimitsOfShape_hypercoverCochainInt
    [∀ n : ℕ, Unique (K.obj (op ⦋n⦌)).I] (ι : Type (max u v w))
    (hqc : ∀ n : ℕ, J.toGrothendieck.IsQuasiCompactObject
      ((K.obj (op ⦋n⦌)).obj default).left) :
    PreservesColimitsOfShape (Discrete ι) (hypercoverCochainIntFunctor J U K) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun p => ?_)
  by_cases hp : 0 ≤ p
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have h1 : PreservesColimitsOfShape (Discrete ι)
        ((sheafSections J.toGrothendieck AddCommGrpCat.{max u v w}).obj
          (op ((K.obj (op ⦋m⦌)).obj default).left)) :=
      Stacks.Sites.preservesColimitsOfShape_discrete_sheafSections_of_isQuasiCompactObject
        J.toGrothendieck _ (hqc m) ι
    have h2 : PreservesColimitsOfShape (Discrete ι)
        (sheafSectionsFunctor J ((K.obj (op ⦋m⦌)).obj default).left) :=
      preservesColimitsOfShape_of_natIso
        (sheafSectionsNatIsoEvaluation J.toGrothendieck AddCommGrpCat.{max u v w})
    exact preservesColimitsOfShape_of_natIso (hypercoverDegreeIntIso J U K m).symm
  · exact preservesColimitsOfShape_of_isZero _ (fun F =>
      isZero_hypercoverCochainInt_X J U K p (by omega) F)

end Degreewise

section TotalComplexQuasiIso

/-- The symmetry isomorphism of the total complex of a bicomplex is natural in the bicomplex. -/
private lemma totalFlipIso_hom_naturality {A : Type*} [Category* A] [Preadditive A]
    {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (φ : Z ⟶ Z') (ψ : Z.flip ⟶ Z'.flip)
    (hψ : ∀ i₂ i₁, (ψ.f i₂).f i₁ = (φ.f i₁).f i₂)
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)]
    [Z.flip.HasTotal (up ℤ)] [Z'.flip.HasTotal (up ℤ)] :
    HomologicalComplex₂.total.map ψ (up ℤ) ≫ (Z'.totalFlipIso (up ℤ)).hom =
      (Z.totalFlipIso (up ℤ)).hom ≫ HomologicalComplex₂.total.map φ (up ℤ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext (up ℤ)
  intro i₂ i₁ h
  have h' : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i₁, i₂) = n := by
    rw [← ComplexShape.π_symm (up ℤ) (up ℤ) (up ℤ) i₁ i₂]; exact h
  have e1 : Z.flip.ιTotal (up ℤ) i₂ i₁ n h ≫
        (HomologicalComplex₂.total.map ψ (up ℤ) ≫ (Z'.totalFlipIso (up ℤ)).hom).f n =
      (ψ.f i₂).f i₁ ≫ (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) i₁ i₂ •
        Z'.ιTotal (up ℤ) i₁ i₂ n h') := by
    rw [HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_map_assoc,
      HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  have e2 : Z.flip.ιTotal (up ℤ) i₂ i₁ n h ≫
        ((Z.totalFlipIso (up ℤ)).hom ≫ HomologicalComplex₂.total.map φ (up ℤ)).f n =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) i₁ i₂ • Z.ιTotal (up ℤ) i₁ i₂ n h') ≫
        (HomologicalComplex₂.total.map φ (up ℤ)).f n := by
    rw [HomologicalComplex.comp_f, ← Category.assoc,
      HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
    rfl
  refine e1.trans (Eq.trans ?_ e2.symm)
  have s1 : (ψ.f i₂).f i₁ ≫ (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) i₁ i₂ •
        Z'.ιTotal (up ℤ) i₁ i₂ n h') =
      (φ.f i₁).f i₂ ≫ (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) i₁ i₂ •
        Z'.ιTotal (up ℤ) i₁ i₂ n h') :=
    congrArg (fun z : (Z.X i₁).X i₂ ⟶ (Z'.X i₁).X i₂ => z ≫ _) (hψ i₂ i₁)
  rw [s1, Linear.comp_units_smul, Linear.units_smul_comp, HomologicalComplex₂.ιTotal_map]

/-- The bicomplex of a complex of abelian sheaves vanishes in hypercover degrees `< 0`. -/
private lemma isZero_flipBicomplex_X (E : CochainComplex (Sheaf J.toGrothendieck
    AddCommGrpCat.{max u v w}) ℤ) (p : ℤ) (hp : p < 0) :
    IsZero ((((hypercoverBicomplexFunctor J U K).obj E).flip).X p) :=
  isZero_complex_of_components _ (fun q => isZero_hypercoverCochainInt_X J U K p hp (E.X q))

/-- The bicomplex of a complex of abelian sheaves bounded below by `n` vanishes in complex
degrees `< n`. -/
private lemma isZero_flipBicomplex_X_X (E : CochainComplex (Sheaf J.toGrothendieck
    AddCommGrpCat.{max u v w}) ℤ) (n : ℤ) [E.IsStrictlyGE n] (p q : ℤ) (hq : q < n) :
    IsZero (((((hypercoverBicomplexFunctor J U K).obj E).flip).X p).X q) :=
  (HomologicalComplex.eval _ (up ℤ) p).map_isZero
    ((hypercoverCochainIntFunctor J U K).map_isZero (E.isZero_of_isStrictlyGE n q hq))

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

/-- **The hypercover total complex of a quasi-isomorphism of bounded below complexes is a
quasi-isomorphism.** -/
private lemma quasiIso_hypercoverTotalCochainFunctor_map
    [∀ n : ℕ, Unique (K.obj (op ⦋n⦌)).I]
    (hexact : ∀ n : ℕ, exactFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max u v w} (sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left))
    {E E' : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ} (g : E ⟶ E')
    [QuasiIso g] (n : ℤ) [E.IsStrictlyGE n] [E'.IsStrictlyGE n] :
    QuasiIso ((hypercoverTotalCochainFunctor J U K).map g) := by
  have hflip : QuasiIso (HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{max u v w} (up ℤ) (up ℤ)).map
        ((hypercoverBicomplexFunctor J U K).map g)) (up ℤ)) := by
    apply quasiIso_total_map_of_bounded _ 0 n
      (isZero_flipBicomplex_X_X J U K E n)
      (isZero_flipBicomplex_X J U K E)
      (isZero_flipBicomplex_X_X J U K E' n)
      (isZero_flipBicomplex_X J U K E')
    intro p
    by_cases hp : 0 ≤ p
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨hlim, hcolim⟩ := exactFunctor_hypercoverCochainInt_comp_eval J U K hexact m
      let G := hypercoverCochainIntFunctor J U K ⋙
        HomologicalComplex.eval AddCommGrpCat.{max u v w} (up ℤ) (m : ℤ)
      have : PreservesFiniteLimits G := hlim
      have : PreservesFiniteColimits G := hcolim
      have : G.PreservesHomology := inferInstance
      have : G.Additive := Functor.additive_of_preserves_binary_products G
      exact HomologicalComplex.quasiIso_map_of_preservesHomology g G
    · have := IsZero.isIso (isZero_flipBicomplex_X J U K E p (by omega))
        (isZero_flipBicomplex_X J U K E' p (by omega))
        (((HomologicalComplex₂.flipFunctor AddCommGrpCat.{max u v w} (up ℤ) (up ℤ)).map
          ((hypercoverBicomplexFunctor J U K).map g)).f p)
      infer_instance
  rw [hypercoverTotalCochainFunctor_map]
  exact quasiIso_of_arrow_mk_iso
    (HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{max u v w} (up ℤ) (up ℤ)).map
        ((hypercoverBicomplexFunctor J U K).map g)) (up ℤ)) _
    (Arrow.isoMk (((hypercoverBicomplexFunctor J U K).obj E).totalFlipIso (up ℤ))
      (((hypercoverBicomplexFunctor J U K).obj E').totalFlipIso (up ℤ))
      (totalFlipIso_hom_naturality ((hypercoverBicomplexFunctor J U K).map g)
        ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{max u v w} (up ℤ) (up ℤ)).map
          ((hypercoverBicomplexFunctor J U K).map g)) (fun _ _ => rfl)).symm)

end TotalComplexQuasiIso

section DerivedUnit

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

/-- **`Θ` inverts quasi-isomorphisms.** The hypercover total complex functor on the bounded below
homotopy category sends a quasi-isomorphism to an isomorphism in `D⁺(Ab)`. -/
private lemma isInvertedBy_hypercoverTotalDerivedFunctor
    [∀ n : ℕ, Unique (K.obj (op ⦋n⦌)).I]
    (hexact : ∀ n : ℕ, exactFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max u v w} (sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left)) :
    (HomotopyCategory.Plus.quasiIso
        (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).IsInvertedBy
      (hypercoverTotalDerivedFunctor J U K) := by
  intro X Y f hf
  obtain ⟨WX, hWX⟩ := X
  obtain ⟨WY, hWY⟩ := Y
  obtain ⟨E, rfl⟩ := HomotopyCategory.quotient_obj_surjective WX
  obtain ⟨E', rfl⟩ := HomotopyCategory.quotient_obj_surjective WY
  rw [HomotopyCategory.plus_quotient_obj_iff] at hWX hWY
  obtain ⟨n, hn⟩ := hWX
  obtain ⟨n', hn'⟩ := hWY
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient
    (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (up ℤ)).map_surjective f.hom
  rw [HomotopyCategory.Plus.quasiIso_iff, ← hg,
    HomotopyCategory.quotient_map_mem_quasiIso_iff] at hf
  have h₁ : CochainComplex.IsStrictlyGE E (min n n') :=
    have := hn
    CochainComplex.isStrictlyGE_of_ge E _ _ (min_le_left n n')
  have h₂ : CochainComplex.IsStrictlyGE E' (min n n') :=
    have := hn'
    CochainComplex.isStrictlyGE_of_ge E' _ _ (min_le_right n n')
  have hqg : QuasiIso g := hf
  have hq : QuasiIso ((hypercoverTotalCochainFunctor J U K).map g) :=
    quasiIso_hypercoverTotalCochainFunctor_map J U K hexact g (min n n')
  have key : HomotopyCategory.Plus.quasiIso AddCommGrpCat.{max u v w}
      ((hypercoverTotalPlusFunctor J U K).map f) := by
    have h0 : ((hypercoverTotalPlusFunctor J U K).map f).hom =
        (hypercoverTotalHomotopyFunctor J U K).map f.hom := rfl
    have hcomp : (hypercoverTotalHomotopyFunctor J U K).map
          ((HomotopyCategory.quotient
            (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (up ℤ)).map g) =
        (HomotopyCategory.quotient AddCommGrpCat.{max u v w} (up ℤ)).map
          ((hypercoverTotalCochainFunctor J U K).map g) := rfl
    rw [HomotopyCategory.Plus.quasiIso_iff, h0, ← hg, hcomp]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
      ((hypercoverTotalCochainFunctor J U K).map g)).2 hq
  exact Localization.inverts DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso AddCommGrpCat.{max u v w}) _ key

variable [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]

omit [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- **The unit of `RΘ` is invertible.** The canonical comparison from the hypercover total
complex functor `Θ` to its right derived functor `RΘ` is an isomorphism. -/
private lemma isIso_hypercoverRightDerivedUnit
    [∀ n : ℕ, Unique (K.obj (op ⦋n⦌)).I]
    (hexact : ∀ n : ℕ, exactFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max u v w} (sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left)) :
    IsIso (hypercoverRightDerivedUnit J U K) :=
  Functor.isIso_of_isRightDerivedFunctor_of_inverts (hypercoverRightDerived J U K)
    (hypercoverRightDerivedUnit J U K)
    (isInvertedBy_hypercoverTotalDerivedFunctor J U K hexact)

end DerivedUnit

section Comparison

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
  [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]
  [∀ n : ℕ, Unique (K.obj (op ⦋n⦌)).I]

/-- **Derived sections on the bounded below homotopy category are the hypercover total
complex**: `RΓ(U, -)` composed with the localization `K⁺ ⥤ D⁺` is naturally isomorphic to the
hypercover total complex functor `Θ`. -/
private def derivedSectionsIsoHypercoverTotalDerived (hK : IsHypercovering J K)
    (hexact : ∀ n : ℕ, exactFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max u v w} (sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left)) :
    DerivedCategory.Plus.Qh ⋙ (sheafSectionsFunctor J U).rightDerivedFunctorPlus ≅
      hypercoverTotalDerivedFunctor J U K := by
  have h1 : IsIso (derivedSectionsToHypercoverRightDerived J U K hK) :=
    NatIso.isIso_of_isIso_app _
  have h2 : IsIso (hypercoverRightDerivedUnit J U K) :=
    isIso_hypercoverRightDerivedUnit J U K hexact
  exact Functor.isoWhiskerLeft DerivedCategory.Plus.Qh
      (asIso (derivedSectionsToHypercoverRightDerived J U K hK)) ≪≫
    (asIso (hypercoverRightDerivedUnit J U K)).symm

/-- **Derived sections of a bounded below complex of abelian sheaves are the hypercover total
complex**, naturally in the complex of sheaves and with values in the unbounded derived category
of abelian groups. -/
private def derivedSectionsPlusIsoHypercoverTotal (hK : IsHypercovering J K)
    (hexact : ∀ n : ℕ, exactFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max u v w} (sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left)) :
    HomotopyCategory.Plus.quotient (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ⋙
        DerivedCategory.Plus.Qh ⋙ (sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι ≅
      CochainComplex.Plus.ι (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ⋙
        hypercoverTotalCochainFunctor J U K ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (derivedSectionsIsoHypercoverTotalDerived J U K hK hexact)
        DerivedCategory.Plus.ι) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι _ ⋙ hypercoverTotalCochainFunctor J U K)
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{max u v w})

end Comparison

end General

section Main

variable {C : Type u} [SmallCategory C] [HasPullbacks C]
  (J : Pretopology C) (U : C) (K : SimplicialObject (FormalCoproduct.{u} (Over U)))
  [HasSheafify J.toGrothendieck AddCommGrpCat.{u}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{u})]

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{u}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{u})] in
/-- The category of abelian sheaves has all coproducts indexed by a type `ι : Type u`. -/
private lemma hasColimitsOfShape_sheaf (ι : Type u) :
    HasColimitsOfShape (Discrete ι) (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
  have : HasColimitsOfSize.{u, u} (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasColimits _
  inferInstance

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{u}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{u})] in
/-- **The hypercover total complex commutes with direct sums.** -/
private lemma preservesColimitsOfShape_hypercoverTotalCochainFunctor
    [∀ n : ℕ, Unique (K.obj (op ⦋n⦌)).I] (ι : Type u)
    (hqc : ∀ n : ℕ, J.toGrothendieck.IsQuasiCompactObject
      ((K.obj (op ⦋n⦌)).obj default).left) :
    PreservesColimitsOfShape (Discrete ι) (hypercoverTotalCochainFunctor J U K) := by
  have hcol := hasColimitsOfShape_sheaf J ι
  have h1 : PreservesColimitsOfShape (Discrete ι) (hypercoverCochainIntFunctor J U K) :=
    preservesColimitsOfShape_hypercoverCochainInt J U K ι hqc
  have h3 : PreservesColimitsOfShape (Discrete ι)
      (HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ)) := by
    constructor
    intro D
    exact CochainComplex.KFlat.preservesColimit_totalFunctor (up ℤ) D
  have h2 : PreservesColimitsOfShape (Discrete ι)
      ((hypercoverCochainIntFunctor J U K).mapHomologicalComplex (up ℤ)) := by
    refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i => ?_)
    have he : PreservesColimitsOfShape (Discrete ι)
        (HomologicalComplex.eval (Sheaf J.toGrothendieck AddCommGrpCat.{u}) (up ℤ) i) :=
      inferInstance
    have hcomp : PreservesColimitsOfShape (Discrete ι)
        (HomologicalComplex.eval (Sheaf J.toGrothendieck AddCommGrpCat.{u}) (up ℤ) i ⋙
          hypercoverCochainIntFunctor J U K) := comp_preservesColimitsOfShape _ _
    exact preservesColimitsOfShape_of_natIso
      (F := HomologicalComplex.eval (Sheaf J.toGrothendieck AddCommGrpCat.{u}) (up ℤ) i ⋙
        hypercoverCochainIntFunctor J U K) (Iso.refl _)
  have h4 : PreservesColimitsOfShape (Discrete ι)
      ((hypercoverCochainIntFunctor J U K).mapHomologicalComplex (up ℤ) ⋙
        HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ)) :=
    comp_preservesColimitsOfShape _ _
  exact preservesColimitsOfShape_of_natIso
    (F := (hypercoverCochainIntFunctor J U K).mapHomologicalComplex (up ℤ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ))
    (Iso.refl _)

/-- The property of a hypercovering `K` of `U` that its term in each degree is a *one-element*
family on an object which is quasi-compact (Stacks 090H) and over which taking sections of
abelian sheaves is exact. -/
public def IsSingletonExactQuasiCompact : Prop :=
  ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I, (∀ j, j = i) ∧
    exactFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{u}) AddCommGrpCat.{u}
      (sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj i).left) ∧
    J.toGrothendieck.IsQuasiCompactObject ((K.obj (op ⦋n⦌)).obj i).left

/-- Derived sections over `U` commute with direct sums: every colimit cocone on a family of
objects of `D⁺(Sh(J, Ab))` is carried by `RΓ(U, -) : D⁺(Sh(J, Ab)) ⥤ D(Ab)` to a colimit cocone
in `D(Ab)`. -/
@[stacks 09A3 "direct sums, as preservation of colimit cocones indexed by a discrete \
category; same hypotheses as the cofan form below"]
public theorem preservesColimitsOfShape_discrete_derivedSectionsPlus
    (hK : IsHypercovering J K) (hcov : IsSingletonExactQuasiCompact J U K) (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι)
      ((sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) := by
  classical
  have hcol := hasColimitsOfShape_sheaf J ι
  let huniq : ∀ n : ℕ, Unique (K.obj (op ⦋n⦌)).I := fun n =>
    ⟨⟨(hcov n).choose⟩, fun j => (hcov n).choose_spec.1 j⟩
  have hexact : ∀ n : ℕ, exactFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{u}) AddCommGrpCat.{u}
      (sheafSectionsFunctor J ((K.obj (op ⦋n⦌)).obj default).left) :=
    fun n => (hcov n).choose_spec.2.1
  have hqc : ∀ n : ℕ, J.toGrothendieck.IsQuasiCompactObject
      ((K.obj (op ⦋n⦌)).obj default).left := fun n => (hcov n).choose_spec.2.2
  have htot : PreservesColimitsOfShape (Discrete ι) (hypercoverTotalCochainFunctor J U K) :=
    preservesColimitsOfShape_hypercoverTotalCochainFunctor J U K ι hqc
  constructor
  intro D
  have key : ∀ (E : ι → DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u})),
      PreservesColimit (Discrete.functor E)
        ((sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) := by
    intro E
    constructor
    intro c hc
    refine ⟨(Cofan.isColimitMapCoconeEquiv
      ((sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) E c).symm ?_⟩
    let N : ℤ := c.pt.property.choose
    have hNS : DerivedCategory.IsGE (DerivedCategory.Plus.ι.obj c.pt) N :=
      c.pt.property.choose_spec
    have hEN : ∀ i, DerivedCategory.IsGE (DerivedCategory.Plus.ι.obj (E i)) N := by
      intro i
      rw [DerivedCategory.isGE_iff]
      intro p hp
      obtain ⟨r, hr⟩ := exists_retraction_of_isColimit_cofan (Cofan.inj c) hc i
      have hz : IsZero ((DerivedCategory.homologyFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{u}) p).obj
          (DerivedCategory.Plus.ι.obj c.pt)) :=
        DerivedCategory.isZero_of_isGE _ N p hp
      have h1 : DerivedCategory.Plus.ι.map (Cofan.inj c i) ≫ DerivedCategory.Plus.ι.map r =
          𝟙 (DerivedCategory.Plus.ι.obj (E i)) := by
        rw [← CategoryTheory.Functor.map_comp, hr, CategoryTheory.Functor.map_id]
      have h2 := congrArg (DerivedCategory.homologyFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{u}) p).map h1
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h2
      rw [IsZero.iff_id_eq_zero, ← h2, hz.eq_of_tgt
        ((DerivedCategory.homologyFunctor (Sheaf J.toGrothendieck AddCommGrpCat.{u}) p).map
          (DerivedCategory.Plus.ι.map (Cofan.inj c i))) 0, Limits.zero_comp]
    have hrep : ∀ i, ∃ (M : CochainComplex
        (Sheaf J.toGrothendieck AddCommGrpCat.{u}) ℤ) (_ : M.IsStrictlyGE N),
        Nonempty (DerivedCategory.Plus.ι.obj (E i) ≅ DerivedCategory.Q.obj M) := fun i =>
      have := hEN i
      DerivedCategory.exists_iso_Q_obj_of_isGE _ N
    choose ℰ hSt hiso using hrep
    have hStI : ∀ i, CochainComplex.IsStrictlyGE (ℰ i) N := hSt
    have hcop : IsColimit (Cofan.mk (∐ ℰ) (Limits.Sigma.ι ℰ)) := coproductIsCoproduct ℰ
    have hGE : CochainComplex.IsStrictlyGE (∐ ℰ) N := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro p hp
      exact isZero_cofan_pt_of_isZero _
        (isColimit_cofan_map_of_preserves (HomologicalComplex.eval
          (Sheaf J.toGrothendieck AddCommGrpCat.{u}) (up ℤ) p) _ hcop)
        (fun j => (ℰ j).isZero_of_isStrictlyGE N p hp)
    let EP : ι → CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
      fun i => ⟨ℰ i, ⟨N, hSt i⟩⟩
    let SP : CochainComplex.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
      ⟨∐ ℰ, ⟨N, hGE⟩⟩
    let incl : ∀ i, EP i ⟶ SP := fun i => ObjectProperty.homMk (Limits.Sigma.ι ℰ i)
    let A' : ι → DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
      fun i => DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj (EP i))
    let T : DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj SP)
    let inj' : ∀ i, A' i ⟶ T := fun i =>
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map (incl i))
    have hQ : IsColimit (Cofan.mk ((DerivedCategory.Q (C :=
        Sheaf J.toGrothendieck AddCommGrpCat.{u})).obj (∐ ℰ))
        (fun i => DerivedCategory.Q.map (Limits.Sigma.ι ℰ i))) :=
      isColimit_cofan_map_of_preserves DerivedCategory.Q _ hcop
    have hd : IsColimit (Cofan.mk T inj') :=
      isColimitOfReflects DerivedCategory.Plus.ι
        ((Cofan.isColimitMapCoconeEquiv DerivedCategory.Plus.ι A' (Cofan.mk T inj')).symm
          (isColimit_cofan_map_of_natIso
            (DerivedCategory.quotientCompQhIso (Sheaf J.toGrothendieck AddCommGrpCat.{u}))
            (Limits.Sigma.ι ℰ) hQ))
    have eiso : ∀ j, E j ≅ A' j := fun j =>
      DerivedCategory.Plus.ι.preimageIso ((hiso j).some ≪≫
        ((DerivedCategory.quotientCompQhIso
          (Sheaf J.toGrothendieck AddCommGrpCat.{u})).app (ℰ j)).symm)
    refine isColimit_mapCofan_of_isColimit_mapCofan
      ((sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      eiso (Cofan.inj c) hc inj' hd ?_
    refine isColimit_cofan_map_of_natIso
      (derivedSectionsPlusIsoHypercoverTotal J U K hK hexact) incl ?_
    exact isColimit_cofan_map_of_preserves
      (hypercoverTotalCochainFunctor J U K ⋙ DerivedCategory.Q) _ hcop
  let f : ι → DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
    fun i => D.obj ⟨i⟩
  let e : D ≅ Discrete.functor f := Discrete.natIso (fun i => Iso.refl (D.obj i))
  have hkey := key f
  exact preservesColimit_of_iso_diagram _ e.symm

/-- Let `U` be an object of a site admitting a hypercovering each of whose terms is a one-element
family on a quasi-compact object over which taking sections of abelian sheaves is exact. Then
`RΓ(U, -) : D⁺(Sh(J, Ab)) ⥤ D(Ab)` commutes with direct sums: if `S`, together with maps
`E i ⟶ S`, is the direct sum of a family `E` of bounded below objects, then `RΓ(U, S)` with the
images of those maps is the direct sum of the `RΓ(U, E i)` in `D(Ab)`. -/
@[stacks 09A3 "direct sums, at an object of a general site admitting a hypercovering by \
one-element families on quasi-compact objects with exact sections --- which is what Tag 09A1 \
provides for the pro-etale site of a quasi-compact quasi-separated scheme, modulo the \
hypotheses that Tag 09A1 itself carries in this library"]
public noncomputable def isColimit_mapCofan_derivedSectionsPlus
    (hK : IsHypercovering J K) (hcov : IsSingletonExactQuasiCompact J U K)
    {ι : Type u}
    {E : ι → DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u})}
    {S : DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u})}
    (inj : ∀ i, E i ⟶ S) (hc : IsColimit (Cofan.mk S inj)) :
    IsColimit (Cofan.mk (DerivedCategory.Plus.ι.obj
        ((sheafSectionsFunctor J U).rightDerivedFunctorPlus.obj S))
      (fun i => DerivedCategory.Plus.ι.map
        ((sheafSectionsFunctor J U).rightDerivedFunctorPlus.map (inj i)))) :=
  haveI := preservesColimitsOfShape_discrete_derivedSectionsPlus J U K hK hcov ι
  (Cofan.isColimitMapCoconeEquiv
    ((sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) E
    (Cofan.mk S inj)) (isColimitOfPreserves _ hc)

/-- Derived sections over `U` carry a homotopy colimit of a system of bounded below complexes of
abelian sheaves to a homotopy colimit in `D(Ab)`. -/
@[stacks 09A3 "homotopy colimits, under the same hypotheses on the hypercovering as the \
direct sums half"]
public theorem isHomotopyColimit_derivedSectionsPlus
    (hK : IsHypercovering J K) (hcov : IsSingletonExactQuasiCompact J U K)
    (F : ℕ ⥤ DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u}))
    [HasCoproduct F.obj]
    {X : DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{u})}
    [HasCoproduct (F ⋙ (sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).obj]
    (h : Pretriangulated.IsHomotopyColimit F X) :
    Pretriangulated.IsHomotopyColimit
      (F ⋙ (sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (((sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι).obj X) := by
  let hcs : ((sheafSectionsFunctor J U).rightDerivedFunctorPlus).CommShift ℤ :=
    Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus _
  have hit : ((sheafSectionsFunctor J U).rightDerivedFunctorPlus).IsTriangulated :=
    Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus _
  have hpres : PreservesColimitsOfShape (Discrete ℕ)
      ((sheafSectionsFunctor J U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) := by
    have h0 := preservesColimitsOfShape_discrete_derivedSectionsPlus J U K hK hcov (ULift.{u} ℕ)
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  exact h.map _

end Main

end Stacks.CategoryTheory.Hypercovering

end
