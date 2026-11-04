module

public import
    StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorUnitality
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationAtlasFaithful
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedCommutative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPullCommutative

/-!
# Laws of descended multiplications, and the laws of the twists on the charts of a relative Proj

In Situation 0849 the twists `𝒪_P(n)` of `P = Proj_X(𝒜)` and their multiplications
`𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` and unit `𝒪_P ⟶ 𝒪_P(0)` are descended along a presentation
`P = P_U/P_R` from those of the twists of Stacks 01NR on the scheme of `P_U`
(`AlgebraicGeometry.Space.RelativeProjSituation.twistModuleMul`,
`AlgebraicGeometry.Space.RelativeProjSituation.twistModuleUnit`), by
`AlgebraicGeometry.Space.presentationDescendedMul` and
`AlgebraicGeometry.Space.presentationDescendedUnit`.  This file proves, for any presentation
`X = U/R`, that descended multiplications and units satisfy the laws of Stacks 084D (associative,
commutative, unital, each up to the identification of the degrees) as soon as the multiplications
and the unit on the scheme of `U` do, and proves those laws for the twists on the scheme of a
base change.

A morphism of quasi-coherent modules on `X` is determined by its inverse image along the atlas
(`AlgebraicGeometry.Space.presentationAtlas_map_injective`).  The inverse image along the atlas
of each side of a law is computed by the defining property of the descended multiplication and
unit, the coherence of Stacks 03EL for algebraic spaces with the structural morphisms
(`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensorCoherence`), and the chart
identifications; this reduces each law to the same law for the attached multiplications on the
representable `yoneda U`.  That law in turn is the image under Stacks 03DX (2) of the law on the
scheme, by the coherence of the tensor identification of Stacks 03DX (2) with the structural
morphisms
(`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorCoherence`,
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorUnitality`).  For
the twists the laws on the scheme are those of the sheaf of graded algebras `⨁_n 𝒪(n)` of
Stacks 01NR, read through the tensor product sheaf of Tag 01CA
(`Stacks.TensorSheafWorld.mulSheaf_assoc`, `Stacks.TensorSheafWorld.mulSheaf_eq_braiding_comp`,
`SheafOfModules.GradedAlgebra.mulSheaf_one_mul`).

## Main results

* `AlgebraicGeometry.Space.mulSheaf_assoc_zariskiRingedSite`,
  `AlgebraicGeometry.Space.mulSheaf_comm_zariskiRingedSite` and
  `AlgebraicGeometry.Space.oneHom_mulSheaf_zariskiRingedSite`: the laws of a sheaf of graded
  algebras on a scheme, with the structural morphisms of the strict structure of Tag 01CA on the
  Zariski ringed site.
* `AlgebraicGeometry.Space.representedTensorChartMul_assoc`,
  `AlgebraicGeometry.Space.representedTensorChartMul_comm` and
  `AlgebraicGeometry.Space.representedTensorChartMul_one_mul`: the laws pass to the modules
  attached by Stacks 03DX (2).
* `AlgebraicGeometry.Space.modulePullback_map_mul_assoc_of_chart` and its companions: the laws
  of a multiplication of `𝒪_X`-modules hold after inverse image along a morphism `f` as soon as
  the inverse images are carried to multiplications satisfying them.
* `AlgebraicGeometry.Space.presentationDescendedMul_assoc`,
  `AlgebraicGeometry.Space.presentationDescendedMul_comm`,
  `AlgebraicGeometry.Space.presentationDescendedUnit_mul` and
  `AlgebraicGeometry.Space.presentationDescendedMul_unit`: **descended multiplications and units
  satisfy the laws of Stacks 084D whenever the multiplications and the unit on the presenting
  scheme do.**
* `AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul_assoc` and its
  companions: the same on the presentation `P = P_U/P_R`, spelled through the base changes.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceMul_assoc`, `twistPieceMul_comm` and
  `twistPieceUnit_mul`: the laws of the twists on the scheme of a base change.

## Implementation notes

The reductions are proved once, by abstract lemmas over monoidal categories in which the
comparison of Stacks 03EL, the chart identifications and the tensor identification of
Stacks 03DX (2) are variables, and instantiated with `refine` and one `exact` per hypothesis;
the instantiation is made at a general presentation, where every module is a variable, and not
at the presentation of the relative Proj, where the kernel exhausts its budget comparing the
concrete objects.

The twists on the scheme of a base change are the pieces of the inverse image of a sheaf of
graded algebras, and their multiplications are its multiplications, by definition; but the
kernel does not check that identification cheaply inside the tensor product of morphisms of
quasi-coherent modules.  The laws on the scheme are therefore proved for an arbitrary family of
quasi-coherent modules and multiplications *equal* to the pieces and multiplications of a sheaf
of graded algebras (`AlgebraicGeometry.Space.quasicoherentMul_assoc_of_eq` and its
companions): the equalities are substituted away in the proof, and the instances supply them by
`rfl` and `HEq.rfl`.

The equations between the structural morphisms of the two spellings of the strict structure of
Tag 01CA in play (at the Zariski ringed site, and at `Stacks.TensorSheafWorld.monoidalCategory`)
are stated between the isomorphisms, where they hold by `rfl` at once; between their underlying
morphisms they exhaust the heartbeat budget.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

section AbstractAtlas

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) (δ : ∀ X Y : C, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
  {G : ℤ → C} {H : ℤ → D} (c : ∀ n, F.obj (G n) ≅ H n)
  (μ : ∀ i j, G i ⊗ G j ⟶ G (i + j)) (ν : ∀ i j, H i ⊗ H j ⟶ H (i + j))
  (hμ : ∀ i j, F.map (μ i j) ≫ (c (i + j)).hom =
    (δ (G i) (G j)).hom ≫ ((c i).hom ⊗ₘ (c j).hom) ≫ ν i j)

omit [MonoidalCategory C] [MonoidalCategory D] in
/-- Chart identifications of a degreewise family commute with the transport along an equality of
degrees. -/
private theorem map_eqToHom_comp_chart_hom {n n' : ℤ} (h : n = n') :
    F.map (eqToHom (congrArg G h)) ≫ (c n').hom = (c n).hom ≫ eqToHom (congrArg H h) := by
  subst h
  simp

include hμ in
/-- **The atlas reduction of associativity**: for a functor `F` with a comparison `δ` of tensor
products compatible with the whiskerings and the associators, multiplications `μ` whose images
under `F` are carried by identifications `c` to multiplications `ν` satisfy the associativity law
under `F` as soon as the `ν` satisfy it. -/
private theorem map_mul_assoc_of_chart
    (hδl : ∀ (X : C) {Y Y' : C} (b : Y ⟶ Y'),
      F.map (X ◁ b) ≫ (δ X Y').hom = (δ X Y).hom ≫ (F.obj X ◁ F.map b))
    (hδr : ∀ {X X' : C} (a : X ⟶ X') (Y : C),
      F.map (a ▷ Y) ≫ (δ X' Y).hom = (δ X Y).hom ≫ (F.map a ▷ F.obj Y))
    (hδa : ∀ X Y Z : C, F.map (α_ X Y Z).hom ≫ (δ X (Y ⊗ Z)).hom ≫ (F.obj X ◁ (δ Y Z).hom) =
      (δ (X ⊗ Y) Z).hom ≫ ((δ X Y).hom ▷ F.obj Z) ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom)
    (hν : ∀ i j k, ν i j ▷ H k ≫ ν (i + j) k =
      (α_ (H i) (H j) (H k)).hom ≫ H i ◁ ν j k ≫ ν i (j + k) ≫
        eqToHom (congrArg H (add_assoc i j k).symm))
    (i j k : ℤ) :
    F.map (μ i j ▷ G k ≫ μ (i + j) k) =
      F.map ((α_ (G i) (G j) (G k)).hom ≫ G i ◁ μ j k ≫ μ i (j + k) ≫
        eqToHom (congrArg G (add_assoc i j k).symm)) := by
  rw [← cancel_mono (c (i + j + k)).hom]
  have eL : F.map (μ i j ▷ G k ≫ μ (i + j) k) ≫ (c (i + j + k)).hom =
      (δ (G i ⊗ G j) (G k)).hom ≫ ((δ (G i) (G j)).hom ▷ F.obj (G k)) ≫
        (((c i).hom ⊗ₘ (c j).hom) ⊗ₘ (c k).hom) ≫ (ν i j ▷ H k) ≫ ν (i + j) k := by
    rw [F.map_comp, Category.assoc, hμ, reassoc_of% (hδr (μ i j) (G k)),
      whiskerRight_comp_tensorHom_assoc, hμ, tensorHom_comp_whiskerRight_assoc,
      whiskerRight_comp_tensorHom_assoc]
  have eR : F.map ((α_ (G i) (G j) (G k)).hom ≫ G i ◁ μ j k ≫ μ i (j + k) ≫
        eqToHom (congrArg G (add_assoc i j k).symm)) ≫ (c (i + j + k)).hom =
      F.map (α_ (G i) (G j) (G k)).hom ≫ (δ (G i) (G j ⊗ G k)).hom ≫
        (F.obj (G i) ◁ (δ (G j) (G k)).hom) ≫ ((c i).hom ⊗ₘ ((c j).hom ⊗ₘ (c k).hom)) ≫
        (H i ◁ ν j k) ≫ ν i (j + k) ≫ eqToHom (congrArg H (add_assoc i j k).symm) := by
    simp only [F.map_comp, Category.assoc]
    rw [map_eqToHom_comp_chart_hom F c (add_assoc i j k).symm, reassoc_of% (hμ i (j + k)),
      reassoc_of% (hδl (G i) (μ j k)), whiskerLeft_comp_tensorHom_assoc, hμ,
      tensorHom_comp_whiskerLeft_assoc, whiskerLeft_comp_tensorHom_assoc]
  rw [eL, eR, reassoc_of% (hδa (G i) (G j) (G k)), hν, associator_naturality_assoc]

include hμ in
/-- **The atlas reduction of commutativity**, the companion of `map_mul_assoc_of_chart` for a
comparison compatible with the braidings. -/
private theorem map_mul_comm_of_chart [BraidedCategory C] [BraidedCategory D]
    (hδb : ∀ X Y : C, F.map (β_ X Y).hom ≫ (δ Y X).hom = (δ X Y).hom ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (hν : ∀ i j, (β_ (H i) (H j)).hom ≫ ν j i = ν i j ≫ eqToHom (congrArg H (add_comm i j)))
    (i j : ℤ) :
    F.map ((β_ (G i) (G j)).hom ≫ μ j i) = F.map (μ i j ≫ eqToHom (congrArg G (add_comm i j))) := by
  rw [← cancel_mono (c (j + i)).hom]
  simp only [F.map_comp, Category.assoc]
  rw [hμ j i, reassoc_of% (hδb (G i) (G j)), ← BraidedCategory.braiding_naturality_assoc, hν,
    map_eqToHom_comp_chart_hom F c (add_comm i j), reassoc_of% (hμ i j)]

include hμ in
/-- **The atlas reduction of the left unit law**, the companion of `map_mul_assoc_of_chart` for a
comparison compatible with the left unitors through an identification `U` of the units. -/
private theorem map_one_mul_of_chart (U : F.obj (𝟙_ C) ≅ 𝟙_ D) (u : 𝟙_ C ⟶ G 0) (ω : 𝟙_ D ⟶ H 0)
    (hu : F.map u ≫ (c 0).hom = U.hom ≫ ω)
    (hδr : ∀ {X X' : C} (a : X ⟶ X') (Y : C),
      F.map (a ▷ Y) ≫ (δ X' Y).hom = (δ X Y).hom ≫ (F.map a ▷ F.obj Y))
    (hδu : ∀ X : C, F.map (λ_ X).hom =
      (δ (𝟙_ C) X).hom ≫ (U.hom ▷ F.obj X) ≫ (λ_ (F.obj X)).hom)
    (hν : ∀ n, ω ▷ H n ≫ ν 0 n = (λ_ (H n)).hom ≫ eqToHom (congrArg H (zero_add n).symm))
    (n : ℤ) :
    F.map (u ▷ G n ≫ μ 0 n) = F.map ((λ_ (G n)).hom ≫ eqToHom (congrArg G (zero_add n).symm)) := by
  rw [← cancel_mono (c (0 + n)).hom]
  simp only [F.map_comp, Category.assoc]
  rw [hμ 0 n, reassoc_of% (hδr u (G n)), whiskerRight_comp_tensorHom_assoc, hu,
    map_eqToHom_comp_chart_hom F c (zero_add n).symm, hδu, Category.assoc, Category.assoc,
    ← leftUnitor_naturality_assoc, ← hν, ← tensorHom_def'_assoc, whiskerRight_comp_tensorHom_assoc]

end AbstractAtlas

/-- **The right unit law of a commutative multiplication follows from the left unit law.** -/
private theorem mul_one_of_one_mul_of_comm {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {G : ℤ → C} (μ : ∀ i j, G i ⊗ G j ⟶ G (i + j)) (u : 𝟙_ C ⟶ G 0)
    (hl : ∀ n, u ▷ G n ≫ μ 0 n = (λ_ (G n)).hom ≫ eqToHom (congrArg G (zero_add n).symm))
    (hc : ∀ i j, (β_ (G i) (G j)).hom ≫ μ j i = μ i j ≫ eqToHom (congrArg G (add_comm i j)))
    (n : ℤ) :
    G n ◁ u ≫ μ n 0 = (ρ_ (G n)).hom ≫ eqToHom (congrArg G (add_zero n).symm) := by
  have e : μ n 0 = (β_ (G n) (G 0)).hom ≫ μ 0 n ≫ eqToHom (congrArg G (add_comm n 0).symm) := by
    rw [reassoc_of% (hc n 0)]
    simp
  rw [e, BraidedCategory.braiding_naturality_right_assoc, reassoc_of% (hl n),
    braiding_leftUnitor_assoc]
  simp

section AbstractChart

variable {Q D : Type*} [Category Q] [Category D] [mD : MonoidalCategory D] {P : ObjectProperty D}
  (A : Q ⥤ P.FullSubcategory) (tO : Q → Q → Q)
  (tH : ∀ {M M' N N' : Q}, (M ⟶ M') → (N ⟶ N') → (tO M N ⟶ tO M' N'))
  (T : ∀ M N : Q, (A.obj (tO M N)).obj ≅ (A.obj M).obj ⊗ (A.obj N).obj)
  (hT : ∀ {M M' N N' : Q} (a : M ⟶ M') (b : N ⟶ N'),
    (A.map (tH a b)).hom ≫ (T M' N').hom = (T M N).hom ≫ ((A.map a).hom ⊗ₘ (A.map b).hom))
  {Mn : ℤ → Q} (m : ∀ i j, tO (Mn i) (Mn j) ⟶ Mn (i + j))

omit mD in
/-- The image of a transport along an equality of degrees has as underlying morphism the transport
of the underlying objects. -/
private theorem map_eqToHom_hom_of_eq {n n' : ℤ} (h : n = n') :
    (A.map (eqToHom (congrArg Mn h))).hom = eqToHom (congrArg (fun p => (A.obj (Mn p)).obj) h) := by
  subst h
  simp

include hT in
/-- **Associativity passes through a monoidal identification**: for a functor `A` into a full
subcategory and an identification `T` of `A(M ⊗ N)` with `A M ⊗ A N`, natural and compatible with
the associators, the morphisms `T⁻¹ ≫ A(m)` attached to associative multiplications `m` are
associative. -/
private theorem chartMul_assoc_of_tensorIso
    (as : ∀ M N K : Q, tO (tO M N) K ≅ tO M (tO N K))
    (hTa : ∀ M N K : Q, (A.map (as M N K).hom).hom ≫ (T M (tO N K)).hom ≫
        ((A.obj M).obj ◁ (T N K).hom) =
      (T (tO M N) K).hom ≫ ((T M N).hom ▷ (A.obj K).obj) ≫
        (α_ (A.obj M).obj (A.obj N).obj (A.obj K).obj).hom)
    (hm : ∀ i j k, tH (m i j) (𝟙 (Mn k)) ≫ m (i + j) k =
      (as _ _ _).hom ≫ tH (𝟙 (Mn i)) (m j k) ≫ m i (j + k) ≫
        eqToHom (congrArg Mn (add_assoc i j k).symm))
    (i j k : ℤ) :
    ((T (Mn i) (Mn j)).inv ≫ (A.map (m i j)).hom) ▷ (A.obj (Mn k)).obj ≫
        (T (Mn (i + j)) (Mn k)).inv ≫ (A.map (m (i + j) k)).hom =
      (α_ (A.obj (Mn i)).obj (A.obj (Mn j)).obj (A.obj (Mn k)).obj).hom ≫
        (A.obj (Mn i)).obj ◁ ((T (Mn j) (Mn k)).inv ≫ (A.map (m j k)).hom) ≫
        (T (Mn i) (Mn (j + k))).inv ≫ (A.map (m i (j + k))).hom ≫
        eqToHom (congrArg (fun p => (A.obj (Mn p)).obj) (add_assoc i j k).symm) := by
  have nR : ((A.map (m i j)).hom ▷ (A.obj (Mn k)).obj) ≫ (T (Mn (i + j)) (Mn k)).inv =
      (T _ _).inv ≫ (A.map (tH (m i j) (𝟙 (Mn k)))).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, hT]
    simp
  have nL : ((A.obj (Mn i)).obj ◁ (A.map (m j k)).hom) ≫ (T (Mn i) (Mn (j + k))).inv =
      (T _ _).inv ≫ (A.map (tH (𝟙 (Mn i)) (m j k))).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, hT]
    simp
  have hA : ((T (Mn i) (Mn j)).inv ▷ (A.obj (Mn k)).obj) ≫ (T _ (Mn k)).inv =
      (α_ _ _ _).hom ≫ ((A.obj (Mn i)).obj ◁ (T (Mn j) (Mn k)).inv) ≫ (T _ _).inv ≫
        (A.map (as (Mn i) (Mn j) (Mn k)).inv).hom := by
    rw [← cancel_epi ((T (Mn i) (Mn j)).hom ▷ _), ← cancel_epi (T (tO (Mn i) (Mn j)) (Mn k)).hom]
    simp only [hom_inv_whiskerRight_assoc, Iso.hom_inv_id]
    rw [← reassoc_of% (hTa (Mn i) (Mn j) (Mn k)), whiskerLeft_hom_inv_assoc, Iso.hom_inv_id_assoc,
      ← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, ObjectProperty.FullSubcategory.id_hom]
  have hc : (A.map (as (Mn i) (Mn j) (Mn k)).inv).hom ≫ (A.map (as (Mn i) (Mn j) (Mn k)).hom).hom =
      𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, ObjectProperty.FullSubcategory.id_hom]
  have e1 := congrArg (fun z => (A.map z).hom) (hm i j k)
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at e1
  rw [comp_whiskerRight, Category.assoc, reassoc_of% nR, reassoc_of% hA, e1, reassoc_of% hc,
    whiskerLeft_comp, Category.assoc, reassoc_of% nL,
    map_eqToHom_hom_of_eq A (add_assoc i j k).symm]

include hT in
/-- **Commutativity passes through a monoidal identification**, the companion of
`chartMul_assoc_of_tensorIso` for an identification compatible with the braidings. -/
private theorem chartMul_comm_of_tensorIso [bD : BraidedCategory D]
    (br : ∀ M N : Q, tO M N ≅ tO N M)
    (hTb : ∀ M N : Q, (A.map (br M N).hom).hom ≫ (T N M).hom =
      (T M N).hom ≫ (β_ (A.obj M).obj (A.obj N).obj).hom)
    (hm : ∀ i j, (br _ _).hom ≫ m j i = m i j ≫ eqToHom (congrArg Mn (add_comm i j)))
    (i j : ℤ) :
    (β_ (A.obj (Mn i)).obj (A.obj (Mn j)).obj).hom ≫ (T (Mn j) (Mn i)).inv ≫
        (A.map (m j i)).hom =
      ((T (Mn i) (Mn j)).inv ≫ (A.map (m i j)).hom) ≫
        eqToHom (congrArg (fun p => (A.obj (Mn p)).obj) (add_comm i j)) := by
  have hB : (β_ (A.obj (Mn i)).obj (A.obj (Mn j)).obj).hom ≫ (T (Mn j) (Mn i)).inv =
      (T (Mn i) (Mn j)).inv ≫ (A.map (br (Mn i) (Mn j)).hom).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, hTb]
  have e1 := congrArg (fun z => (A.map z).hom) (hm i j)
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at e1
  rw [reassoc_of% hB, e1, map_eqToHom_hom_of_eq A (add_comm i j), Category.assoc]

include hT in
/-- **The left unit law passes through a monoidal identification**, the companion of
`chartMul_assoc_of_tensorIso` for an identification compatible with the left unitors through an
identification `TU` of the units. -/
private theorem chartMul_one_mul_of_tensorIso (qU : Q) (TU : (A.obj qU).obj ≅ 𝟙_ D)
    (ql : ∀ M : Q, tO qU M ≅ M)
    (hTl : ∀ M : Q, (A.map (ql M).hom).hom =
      (T qU M).hom ≫ (TU.hom ▷ (A.obj M).obj) ≫ (λ_ (A.obj M).obj).hom)
    (u : qU ⟶ Mn 0)
    (hm : ∀ n, tH u (𝟙 (Mn n)) ≫ m 0 n = (ql (Mn n)).hom ≫ eqToHom (congrArg Mn (zero_add n).symm))
    (n : ℤ) :
    (TU.inv ≫ (A.map u).hom) ▷ (A.obj (Mn n)).obj ≫ (T (Mn 0) (Mn n)).inv ≫
        (A.map (m 0 n)).hom =
      (λ_ (A.obj (Mn n)).obj).hom ≫
        eqToHom (congrArg (fun p => (A.obj (Mn p)).obj) (zero_add n).symm) := by
  have nR : ((A.map u).hom ▷ (A.obj (Mn n)).obj) ≫ (T (Mn 0) (Mn n)).inv =
      (T qU (Mn n)).inv ≫ (A.map (tH u (𝟙 (Mn n)))).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, hT]
    simp
  have e1 := congrArg (fun z => (A.map z).hom) (hm n)
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at e1
  rw [comp_whiskerRight, Category.assoc, reassoc_of% nR, e1, hTl,
    map_eqToHom_hom_of_eq A (zero_add n).symm]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, inv_hom_whiskerRight_assoc]

end AbstractChart

/-- A degreewise family of objects of a full subcategory, transported along an equality of
degrees, has as underlying morphism the transport of the underlying objects. -/
private theorem fullSubcategory_eqToHom_hom {C' : Type*} [Category C'] {P : ObjectProperty C'}
    (f : ℤ → P.FullSubcategory) {n n' : ℤ} (h : n = n') :
    (eqToHom (congrArg f h)).hom = eqToHom (congrArg (fun p => (f p).obj) h) := by
  subst h
  rfl

/-- A factorization `m = b ≫ m' ≫ eqToHom _` through the exchange of two degrees, solved for
`b ≫ m'`. -/
private theorem comp_eq_of_eq_comp_eqToHom {C' : Type*} [Category C'] (G : ℤ → C') {X Y : C'}
    {i j : ℤ} (b : X ⟶ Y) (mji : Y ⟶ G (j + i)) (mij : X ⟶ G (i + j))
    (h : mij = b ≫ mji ≫ eqToHom (congrArg G (add_comm j i))) :
    b ≫ mji = mij ≫ eqToHom (congrArg G (add_comm i j)) := by
  rw [h]
  simp

universe u m

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra)
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

/-- **The multiplication of a sheaf of graded algebras on a scheme is associative**, as an
equation of morphisms out of `(A_i ⊗ A_j) ⊗ A_k`, with the tensor products of morphisms spelled
through the tensor bifunctor of Tag 0GMW and the associator that of the strict structure of
Tag 01CA on the Zariski ringed site. -/
theorem mulSheaf_assoc_zariskiRingedSite {W : Scheme.{u}} (G : SchemeGradedAlgebra W)
    (i j k : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        W.zariskiRingedSite.toRingedTopos.O).map
          (SheafOfModules.GradedAlgebra.mulSheaf G i j)).app (G.piece k) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          W.zariskiRingedSite.toRingedTopos.O).obj (G.piece (i + j))).map (𝟙 (G.piece k))) ≫
      SheafOfModules.GradedAlgebra.mulSheaf G (i + j) k =
    (MonoidalCategoryStruct.associator (self :=
        ((Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
          W.zariskiRingedSite.toRingedTopos.O).toMonoidalCategoryStruct))
        (G.piece i) (G.piece j) (G.piece k)).hom ≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          W.zariskiRingedSite.toRingedTopos.O).map (𝟙 (G.piece i))).app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            W.zariskiRingedSite.toRingedTopos.O).obj (G.piece j)).obj (G.piece k)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          W.zariskiRingedSite.toRingedTopos.O).obj (G.piece i)).map
            (SheafOfModules.GradedAlgebra.mulSheaf G j k)) ≫
      SheafOfModules.GradedAlgebra.mulSheaf G i (j + k) ≫
      eqToHom (congrArg G.piece (add_assoc i j k).symm) := by
  have h1 := Stacks.SheafOfModules.Strict.whiskerRight_eq_tensorSheafBifunctor_map
    W.zariskiRingedSite.toRingedTopos.O (SheafOfModules.GradedAlgebra.mulSheaf G i j) (G.piece k)
  have h2 := Stacks.TensorSheafWorld.mulSheaf_assoc W.sheaf
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf W.sheaf) G i j k
  have h3 := Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map
        W.zariskiRingedSite.toRingedTopos.O (G.piece i)
        (SheafOfModules.GradedAlgebra.mulSheaf G j k)
  have c2 : MonoidalCategoryStruct.associator (self :=
        ((Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
          W.zariskiRingedSite.toRingedTopos.O).toMonoidalCategoryStruct))
        (G.piece i) (G.piece j) (G.piece k) =
      MonoidalCategoryStruct.associator (self :=
        ((Stacks.TensorSheafWorld.monoidalCategory W.sheaf).toMonoidalCategoryStruct))
        (G.piece i) (G.piece j) (G.piece k) := rfl
  refine Eq.trans ?_ (h2.trans ?_)
  · exact congrArg (fun z => z ≫ SheafOfModules.GradedAlgebra.mulSheaf G (i + j) k) h1.symm
  · refine Eq.trans (congrArg (fun z => z ≫ _) (congrArg Iso.hom c2.symm)) ?_
    exact congrArg (fun z => _ ≫ z ≫ SheafOfModules.GradedAlgebra.mulSheaf G i (j + k) ≫
      eqToHom (congrArg G.piece (add_assoc i j k).symm)) h3


/-- **The multiplication of a sheaf of graded algebras on a scheme whose multiplication commutes on
homogeneous local sections is commutative**, as an equation of morphisms out of `A_i ⊗ A_j`, with
the symmetry constraint of the strict structure of Tag 01CA on the Zariski ringed site. -/
theorem mulSheaf_comm_zariskiRingedSite {W : Scheme.{u}} (G : SchemeGradedAlgebra W)
    (hG : ∀ (p q : ℤ) (U : (TopologicalSpace.Opens W.carrier)ᵒᵖ) (x : (G.piece p).val.obj U)
      (y : (G.piece q).val.obj U), HEq ((G.mul p q).app U x y) ((G.mul q p).app U y x))
    (i j : ℤ) :
    (BraidedCategory.braiding (self := Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf
        W.zariskiRingedSite.toRingedTopos.O) (G.piece i) (G.piece j)).hom ≫
        SheafOfModules.GradedAlgebra.mulSheaf G j i =
      SheafOfModules.GradedAlgebra.mulSheaf G i j ≫ eqToHom (congrArg G.piece (add_comm i j)) := by
  have h := Stacks.TensorSheafWorld.mulSheaf_eq_braiding_comp W.toRingedSpace G i j hG
  have c : BraidedCategory.braiding (self := Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf
        W.zariskiRingedSite.toRingedTopos.O) (G.piece i) (G.piece j) =
      BraidedCategory.braiding (self := Stacks.PullbackTensorCoherence.braidedCategory
        W.toRingedSpace) (G.piece i) (G.piece j) := rfl
  exact comp_eq_of_eq_comp_eqToHom G.piece _ _ _
    (h.trans (congrArg (fun z => z ≫ SheafOfModules.GradedAlgebra.mulSheaf G j i ≫
      eqToHom (congrArg G.piece (add_comm j i))) (congrArg Iso.hom c.symm)))


/-- **The left unit law of a sheaf of graded algebras on a scheme**, as an equation of morphisms
out of `𝒪 ⊗ A_n`, with the tensor products of morphisms spelled through the tensor bifunctor of
Tag 0GMW and the left unitor that of the strict structure of Tag 01CA on the Zariski ringed
site. -/
theorem oneHom_mulSheaf_zariskiRingedSite {W : Scheme.{u}} (G : SchemeGradedAlgebra W) (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        W.zariskiRingedSite.toRingedTopos.O).map
          (SheafOfModules.GradedAlgebra.oneHom G)).app (G.piece n) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          W.zariskiRingedSite.toRingedTopos.O).obj (G.piece 0)).map (𝟙 (G.piece n))) ≫
      SheafOfModules.GradedAlgebra.mulSheaf G 0 n =
    (MonoidalCategoryStruct.leftUnitor (self :=
        ((Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
          W.zariskiRingedSite.toRingedTopos.O).toMonoidalCategoryStruct)) (G.piece n)).hom ≫
      eqToHom (congrArg G.piece (zero_add n).symm) := by
  have h1 := Stacks.SheafOfModules.Strict.whiskerRight_eq_tensorSheafBifunctor_map
    W.zariskiRingedSite.toRingedTopos.O (SheafOfModules.GradedAlgebra.oneHom G) (G.piece n)
  have h2 := SheafOfModules.GradedAlgebra.mulSheaf_one_mul (Osharp := W.sheaf) G
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf W.sheaf) n
  have c2 : MonoidalCategoryStruct.leftUnitor (self :=
        ((Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
          W.zariskiRingedSite.toRingedTopos.O).toMonoidalCategoryStruct)) (G.piece n) =
      MonoidalCategoryStruct.leftUnitor (self :=
        ((Stacks.TensorSheafWorld.monoidalCategory W.sheaf).toMonoidalCategoryStruct))
        (G.piece n) := rfl
  refine Eq.trans ?_ (h2.trans ?_)
  · exact congrArg (fun z => z ≫ SheafOfModules.GradedAlgebra.mulSheaf G 0 n) h1.symm
  · exact congrArg (fun z => z ≫ eqToHom (congrArg G.piece (zero_add n).symm))
      (congrArg Iso.hom c2.symm)

section Chart

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **Associative multiplications of quasi-coherent modules on a scheme give associative
multiplications of the attached modules.**  For a degreewise family `M_n` of quasi-coherent
modules on the scheme underlying `U` with multiplications `m : M_i ⊗ M_j ⟶ M_{i+j}` satisfying
the associativity law of the tensor product sheaf of Tag 01CA, the morphisms
`M_i^a ⊗ M_j^a ⟶ M_{i+j}^a` of `AlgebraicGeometry.Space.representedTensorChartMul` attached by
Stacks 03DX (2) satisfy the associativity law of `𝒪_{yoneda U}`-modules. -/
theorem representedTensorChartMul_assoc
    {Mn : ℤ → (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : ∀ i j, quasicoherentTensorObj B S hS U (Mn i) (Mn j) ⟶ Mn (i + j))
    (hm : ∀ i j k, quasicoherentTensorHom B S hS U (m i j) (𝟙 (Mn k)) ≫ m (i + j) k =
      (quasicoherentAssociator B S hS U (Mn i) (Mn j) (Mn k)).hom ≫
        quasicoherentTensorHom B S hS U (𝟙 (Mn i)) (m j k) ≫ m i (j + k) ≫
        eqToHom (congrArg Mn (add_assoc i j k).symm))
    (i j k : ℤ) :
    MonoidalCategoryStruct.whiskerRight (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        (representedTensorChartMul B S hS (m i j))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn k)).obj ≫
      representedTensorChartMul B S hS (m (i + j) k) =
    (MonoidalCategoryStruct.associator (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn i)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn j)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn k)).obj).hom ≫
      MonoidalCategoryStruct.whiskerLeft (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn i)).obj
        (representedTensorChartMul B S hS (m j k)) ≫
      representedTensorChartMul B S hS (m i (j + k)) ≫
      eqToHom (congrArg (fun p => ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
        (Mn p)).obj) (add_assoc i j k).symm) :=
  chartMul_assoc_of_tensorIso (D := Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (mD := modulesMonoidalCategory B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (representedQuasicoherentSchemeEquivalence B S hS U).functor (quasicoherentTensorObj B S hS U)
    (fun {_ _ _ _} a b => quasicoherentTensorHom B S hS U a b)
    (representedQuasicoherentSchemeTensorIso B S hS U)
    (fun {_ _ _ _} a b => representedQuasicoherentSchemeTensorIso_hom_naturality B S hS U a b) m
    (quasicoherentAssociator B S hS U)
    (representedQuasicoherentSchemeTensorIso_associativity B S hS U)
    hm i j k

/-- **Commutative multiplications of quasi-coherent modules on a scheme give commutative
multiplications of the attached modules**: the companion of
`AlgebraicGeometry.Space.representedTensorChartMul_assoc` for the symmetry constraints. -/
theorem representedTensorChartMul_comm
    {Mn : ℤ → (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : ∀ i j, quasicoherentTensorObj B S hS U (Mn i) (Mn j) ⟶ Mn (i + j))
    (hm : ∀ i j, (quasicoherentBraiding B S hS U (Mn i) (Mn j)).hom ≫ m j i =
      m i j ≫ eqToHom (congrArg Mn (add_comm i j)))
    (i j : ℤ) :
    (BraidedCategory.braiding (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn i)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn j)).obj).hom ≫
      representedTensorChartMul B S hS (m j i) =
    representedTensorChartMul B S hS (m i j) ≫
      eqToHom (congrArg (fun p => ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
        (Mn p)).obj) (add_comm i j)) :=
  chartMul_comm_of_tensorIso (D := Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (mD := modulesMonoidalCategory B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (bD := modulesBraidedCategory B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (representedQuasicoherentSchemeEquivalence B S hS U).functor (quasicoherentTensorObj B S hS U)
    (fun {_ _ _ _} a b => quasicoherentTensorHom B S hS U a b)
    (representedQuasicoherentSchemeTensorIso B S hS U)
    (fun {_ _ _ _} a b => representedQuasicoherentSchemeTensorIso_hom_naturality B S hS U a b) m
    (quasicoherentBraiding B S hS U) (representedQuasicoherentSchemeTensorIso_braiding B S hS U)
    hm i j

/-- **A unit for multiplications of quasi-coherent modules on a scheme gives a unit for the
attached multiplications**: if `u : 𝒪_U ⟶ M_0` satisfies the left unit law for `m` with the left
unitor of the tensor product sheaf of Tag 01CA, then the attached
`AlgebraicGeometry.Space.representedUnitChartHom` satisfies the left unit law for the morphisms of
`AlgebraicGeometry.Space.representedTensorChartMul` with the left unitor of
`𝒪_{yoneda U}`-modules. -/
theorem representedTensorChartMul_one_mul
    {Mn : ℤ → (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : ∀ i j, quasicoherentTensorObj B S hS U (Mn i) (Mn j) ⟶ Mn (i + j))
    (u : quasicoherentUnitObj B S hS U ⟶ Mn 0)
    (hm : ∀ n, quasicoherentTensorHom B S hS U u (𝟙 (Mn n)) ≫ m 0 n =
      (quasicoherentLeftUnitor B S hS U (Mn n)).hom ≫ eqToHom (congrArg Mn (zero_add n).symm))
    (n : ℤ) :
    MonoidalCategoryStruct.whiskerRight (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        (representedUnitChartHom B S hS u)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn n)).obj ≫
      representedTensorChartMul B S hS (m 0 n) =
    (MonoidalCategoryStruct.leftUnitor (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj (Mn n)).obj).hom ≫
      eqToHom (congrArg (fun p => ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
        (Mn p)).obj) (zero_add n).symm) :=
  chartMul_one_mul_of_tensorIso (D := Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (mD := modulesMonoidalCategory B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (representedQuasicoherentSchemeEquivalence B S hS U).functor (quasicoherentTensorObj B S hS U)
    (fun {_ _ _ _} a b => quasicoherentTensorHom B S hS U a b)
    (representedQuasicoherentSchemeTensorIso B S hS U)
    (fun {_ _ _ _} a b => representedQuasicoherentSchemeTensorIso_hom_naturality B S hS U a b) m
    (quasicoherentUnitObj B S hS U) (representedQuasicoherentSchemeUnitIso B S hS U)
    (quasicoherentLeftUnitor B S hS U)
    (representedQuasicoherentSchemeTensorIso_leftUnitality B S hS U)
    u hm n

end Chart


section QuasicoherentPieces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  (G : SchemeGradedAlgebra ((BigFppfOver.toScheme B S hS).obj U))
  (hq : ∀ n, (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) (G.piece n))

/-- **The multiplication of a sheaf of graded algebras with quasi-coherent pieces on the scheme
underlying `U` is associative**, as an equation of morphisms of quasi-coherent modules out of
`(A_i ⊗ A_j) ⊗ A_k`. -/
theorem quasicoherentMulSheaf_assoc (i j k : ℤ) :
    quasicoherentTensorHom B S hS U
        (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i j) :
          quasicoherentTensorObj B S hS U ⟨G.piece i, hq i⟩ ⟨G.piece j, hq j⟩ ⟶
            ⟨G.piece (i + j), hq (i + j)⟩)
        (𝟙 (⟨G.piece k, hq k⟩ : (SheafOfModules.isQuasicoherent
          ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)) ≫
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G (i + j) k) :
          quasicoherentTensorObj B S hS U ⟨G.piece (i + j), hq (i + j)⟩ ⟨G.piece k, hq k⟩ ⟶
            ⟨G.piece (i + j + k), hq (i + j + k)⟩) =
    (quasicoherentAssociator B S hS U ⟨G.piece i, hq i⟩ ⟨G.piece j, hq j⟩ ⟨G.piece k, hq k⟩).hom ≫
      quasicoherentTensorHom B S hS U
        (𝟙 (⟨G.piece i, hq i⟩ : (SheafOfModules.isQuasicoherent
          ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory))
        (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G j k) :
          quasicoherentTensorObj B S hS U ⟨G.piece j, hq j⟩ ⟨G.piece k, hq k⟩ ⟶
            ⟨G.piece (j + k), hq (j + k)⟩) ≫
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i (j + k)) :
          quasicoherentTensorObj B S hS U ⟨G.piece i, hq i⟩ ⟨G.piece (j + k), hq (j + k)⟩ ⟶
            ⟨G.piece (i + (j + k)), hq (i + (j + k))⟩) ≫
      eqToHom (congrArg (fun n => (⟨G.piece n, hq n⟩ : (SheafOfModules.isQuasicoherent
          ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory))
        (add_assoc i j k).symm) := by
  refine ObjectProperty.hom_ext _ ?_
  refine Eq.trans ?_ (congrArg (fun z => _ ≫ _ ≫
      (SheafOfModules.GradedAlgebra.mulSheaf G i (j + k)) ≫ z)
    (fullSubcategory_eqToHom_hom (fun n => (⟨G.piece n, hq n⟩ : (SheafOfModules.isQuasicoherent
          ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory))
      (add_assoc i j k).symm).symm)
  exact mulSheaf_assoc_zariskiRingedSite G i j k

/-- **The multiplication of a sheaf of graded algebras with quasi-coherent pieces on the scheme
underlying `U` is commutative** whenever it commutes on homogeneous local sections, as an
equation of morphisms of quasi-coherent modules out of `A_i ⊗ A_j`. -/
theorem quasicoherentMulSheaf_comm
    (hG : ∀ (p q : ℤ) (V : (TopologicalSpace.Opens ((BigFppfOver.toScheme B S hS).obj U).carrier)ᵒᵖ)
      (x : (G.piece p).val.obj V) (y : (G.piece q).val.obj V),
      HEq ((G.mul p q).app V x y) ((G.mul q p).app V y x)) (i j : ℤ) :
    (quasicoherentBraiding B S hS U ⟨G.piece i, hq i⟩ ⟨G.piece j, hq j⟩).hom ≫
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G j i) :
          quasicoherentTensorObj B S hS U ⟨G.piece j, hq j⟩ ⟨G.piece i, hq i⟩ ⟶
            ⟨G.piece (j + i), hq (j + i)⟩) =
    (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i j) :
          quasicoherentTensorObj B S hS U ⟨G.piece i, hq i⟩ ⟨G.piece j, hq j⟩ ⟶
            ⟨G.piece (i + j), hq (i + j)⟩) ≫
      eqToHom (congrArg (fun n => (⟨G.piece n, hq n⟩ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)) (add_comm i j)) := by
  refine ObjectProperty.hom_ext _ ?_
  refine Eq.trans ?_ (congrArg (fun z => SheafOfModules.GradedAlgebra.mulSheaf G i j ≫ z)
    (fullSubcategory_eqToHom_hom (fun n => (⟨G.piece n, hq n⟩ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)) (add_comm i j)).symm)
  exact mulSheaf_comm_zariskiRingedSite G hG i j

/-- **The left unit law of a sheaf of graded algebras with quasi-coherent pieces on the scheme
underlying `U`**, as an equation of morphisms of quasi-coherent modules out of `𝒪 ⊗ A_n`. -/
theorem quasicoherentOneHom_mulSheaf (n : ℤ) :
    quasicoherentTensorHom B S hS U
        (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.oneHom G) :
          quasicoherentUnitObj B S hS U ⟶ ⟨G.piece 0, hq 0⟩)
        (𝟙 (⟨G.piece n, hq n⟩ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)) ≫
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G 0 n) :
          quasicoherentTensorObj B S hS U ⟨G.piece 0, hq 0⟩ ⟨G.piece n, hq n⟩ ⟶
            ⟨G.piece (0 + n), hq (0 + n)⟩) =
    (quasicoherentLeftUnitor B S hS U ⟨G.piece n, hq n⟩).hom ≫
      eqToHom (congrArg (fun p => (⟨G.piece p, hq p⟩ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)) (zero_add n).symm) := by
  refine ObjectProperty.hom_ext _ ?_
  refine Eq.trans ?_ (congrArg (fun z => _ ≫ z)
    (fullSubcategory_eqToHom_hom (fun p => (⟨G.piece p, hq p⟩ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)) (zero_add n).symm).symm)
  exact oneHom_mulSheaf_zariskiRingedSite G n

variable {G hq}

/-- `AlgebraicGeometry.Space.quasicoherentMulSheaf_assoc` for a family of quasi-coherent modules
equal to the pieces of `G` and multiplications equal to those of `G`. -/
theorem quasicoherentMul_assoc_of_eq {Mn : ℤ → (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (hMn : Mn = fun n => ⟨G.piece n, hq n⟩)
    (m : ∀ i j, quasicoherentTensorObj B S hS U (Mn i) (Mn j) ⟶ Mn (i + j))
    (hm : ∀ i j, HEq (m i j) (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i j) :
      quasicoherentTensorObj B S hS U ⟨G.piece i, hq i⟩ ⟨G.piece j, hq j⟩ ⟶
        ⟨G.piece (i + j), hq (i + j)⟩))
    (i j k : ℤ) :
    quasicoherentTensorHom B S hS U (m i j) (𝟙 (Mn k)) ≫ m (i + j) k =
      (quasicoherentAssociator B S hS U (Mn i) (Mn j) (Mn k)).hom ≫
        quasicoherentTensorHom B S hS U (𝟙 (Mn i)) (m j k) ≫ m i (j + k) ≫
        eqToHom (congrArg Mn (add_assoc i j k).symm) := by
  subst hMn
  obtain rfl : m = fun i j => ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i j) :=
    funext fun i => funext fun j => eq_of_heq (hm i j)
  exact quasicoherentMulSheaf_assoc B S hS U G hq i j k

/-- `AlgebraicGeometry.Space.quasicoherentMulSheaf_comm` for a family of quasi-coherent modules
equal to the pieces of `G` and multiplications equal to those of `G`. -/
theorem quasicoherentMul_comm_of_eq
    (hG : ∀ (p q : ℤ) (V : (TopologicalSpace.Opens ((BigFppfOver.toScheme B S hS).obj U).carrier)ᵒᵖ)
      (x : (G.piece p).val.obj V) (y : (G.piece q).val.obj V),
      HEq ((G.mul p q).app V x y) ((G.mul q p).app V y x))
    {Mn : ℤ → (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (hMn : Mn = fun n => ⟨G.piece n, hq n⟩)
    (m : ∀ i j, quasicoherentTensorObj B S hS U (Mn i) (Mn j) ⟶ Mn (i + j))
    (hm : ∀ i j, HEq (m i j) (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i j) :
      quasicoherentTensorObj B S hS U ⟨G.piece i, hq i⟩ ⟨G.piece j, hq j⟩ ⟶
        ⟨G.piece (i + j), hq (i + j)⟩))
    (i j : ℤ) :
    (quasicoherentBraiding B S hS U (Mn i) (Mn j)).hom ≫ m j i =
      m i j ≫ eqToHom (congrArg Mn (add_comm i j)) := by
  subst hMn
  obtain rfl : m = fun i j => ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i j) :=
    funext fun i => funext fun j => eq_of_heq (hm i j)
  exact quasicoherentMulSheaf_comm B S hS U G hq hG i j

/-- `AlgebraicGeometry.Space.quasicoherentOneHom_mulSheaf` for a family of quasi-coherent
modules equal to the pieces of `G`, a unit equal to that of `G` and multiplications equal to those
of `G`. -/
theorem quasicoherentOne_mul_of_eq {Mn : ℤ → (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (hMn : Mn = fun n => ⟨G.piece n, hq n⟩)
    (m : ∀ i j, quasicoherentTensorObj B S hS U (Mn i) (Mn j) ⟶ Mn (i + j))
    (hm : ∀ i j, HEq (m i j) (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i j) :
      quasicoherentTensorObj B S hS U ⟨G.piece i, hq i⟩ ⟨G.piece j, hq j⟩ ⟶
        ⟨G.piece (i + j), hq (i + j)⟩))
    (u : quasicoherentUnitObj B S hS U ⟶ Mn 0)
    (hu : HEq u (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.oneHom G) :
      quasicoherentUnitObj B S hS U ⟶ ⟨G.piece 0, hq 0⟩))
    (n : ℤ) :
    quasicoherentTensorHom B S hS U u (𝟙 (Mn n)) ≫ m 0 n =
      (quasicoherentLeftUnitor B S hS U (Mn n)).hom ≫ eqToHom (congrArg Mn (zero_add n).symm) := by
  subst hMn
  obtain rfl : m = fun i j => ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf G i j) :=
    funext fun i => funext fun j => eq_of_heq (hm i j)
  obtain rfl := eq_of_heq hu
  exact quasicoherentOneHom_mulSheaf B S hS U G hq n

end QuasicoherentPieces





section AtlasReduction

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : Y ⟶ X) {G : ℤ → Modules.{u, u} B S hS X.1 X.2} {H : ℤ → Modules.{u, u} B S hS Y.1 Y.2}
  (c : ∀ n, (modulePullback B S hS f).obj (G n) ≅ H n)
  (μ : ∀ i j, G i ⊗ G j ⟶ G (i + j)) (ν : ∀ i j, H i ⊗ H j ⟶ H (i + j))
  (hμ : ∀ i j, (modulePullback B S hS f).map (μ i j) ≫ (c (i + j)).hom =
    (modulePullbackTensorIso B S hS f (G i) (G j)).hom ≫ ((c i).hom ⊗ₘ (c j).hom) ≫ ν i j)

include hμ in
/-- **The inverse image of a multiplication carried to an associative one is associative**: for
`f` and multiplications `μ` of `𝒪_X`-modules whose inverse
images along `f` are carried by identifications `c` to associative multiplications `ν`, the
inverse images of the two sides of the associativity law of `μ` agree. -/
theorem modulePullback_map_mul_assoc_of_chart
    (hν : ∀ i j k, ν i j ▷ H k ≫ ν (i + j) k =
      (α_ (H i) (H j) (H k)).hom ≫ H i ◁ ν j k ≫ ν i (j + k) ≫
        eqToHom (congrArg H (add_assoc i j k).symm))
    (i j k : ℤ) :
    (modulePullback B S hS f).map (μ i j ▷ G k ≫ μ (i + j) k) =
      (modulePullback B S hS f).map ((α_ (G i) (G j) (G k)).hom ≫ G i ◁ μ j k ≫ μ i (j + k) ≫
        eqToHom (congrArg G (add_assoc i j k).symm)) :=
  map_mul_assoc_of_chart (modulePullback B S hS f) (modulePullbackTensorIso B S hS f) c μ ν hμ
    (modulePullbackTensorIso_whiskerLeft_naturality B S hS f)
    (modulePullbackTensorIso_whiskerRight_naturality B S hS f)
    (modulePullbackTensorIso_associativity B S hS f) hν i j k

include hμ in
/-- **The inverse image of a multiplication carried to a commutative one is commutative**: the
companion of `AlgebraicGeometry.Space.modulePullback_map_mul_assoc_of_chart` for the symmetry
constraints. -/
theorem modulePullback_map_mul_comm_of_chart
    (hν : ∀ i j, (β_ (H i) (H j)).hom ≫ ν j i = ν i j ≫ eqToHom (congrArg H (add_comm i j)))
    (i j : ℤ) :
    (modulePullback B S hS f).map ((β_ (G i) (G j)).hom ≫ μ j i) =
      (modulePullback B S hS f).map (μ i j ≫ eqToHom (congrArg G (add_comm i j))) :=
  map_mul_comm_of_chart (modulePullback B S hS f) (modulePullbackTensorIso B S hS f) c μ ν hμ
    (modulePullbackTensorIso_braiding B S hS f) hν i j

include hμ in
/-- **The inverse image of a unit carried to a unit is a unit**: the companion of
`AlgebraicGeometry.Space.modulePullback_map_mul_assoc_of_chart` for the left unit law, the units
being matched by Stacks 03LU for `f`. -/
theorem modulePullback_map_one_mul_of_chart (u : 𝟙_ _ ⟶ G 0) (ω : 𝟙_ _ ⟶ H 0)
    (hu : (modulePullback B S hS f).map u ≫ (c 0).hom = (modulePullbackUnitIso B S hS f).hom ≫ ω)
    (hν : ∀ n, ω ▷ H n ≫ ν 0 n = (λ_ (H n)).hom ≫ eqToHom (congrArg H (zero_add n).symm))
    (n : ℤ) :
    (modulePullback B S hS f).map (u ▷ G n ≫ μ 0 n) =
      (modulePullback B S hS f).map ((λ_ (G n)).hom ≫ eqToHom (congrArg G (zero_add n).symm)) :=
  map_one_mul_of_chart (modulePullback B S hS f) (modulePullbackTensorIso B S hS f) c μ ν hμ
    (modulePullbackUnitIso B S hS f) u ω hu
    (modulePullbackTensorIso_whiskerRight_naturality B S hS f)
    (modulePullbackTensorIso_leftUnitality B S hS f) hν n

end AtlasReduction


section PresentationLaws

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property) {Mn : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (τ : ∀ n, quasicoherentPullbackObj B S hS P.target (Mn n) ⟶
    quasicoherentPullbackObj B S hS P.source (Mn n))
  (hc : ∀ n, PresentationSchemeCocycle P (Mn n) (τ n))
  (hu : ∀ n, PresentationSchemeUnit P (Mn n) (τ n))
  (m : ∀ i j, quasicoherentTensorObj B S hS P.U (Mn i) (Mn j) ⟶ Mn (i + j))
  (hbt : ∀ i j, RepresentedC3TensorCompat B S hS P.target (Mn i) (Mn j))
  (hbs : ∀ i j, RepresentedC3TensorCompat B S hS P.source (Mn i) (Mn j))
  (hm : ∀ i j, (quasicoherentPullbackTensorIso B S hS P.target (Mn i) (Mn j)).inv ≫
      quasicoherentPullbackMap B S hS P.target (m i j) ≫ τ (i + j) =
    quasicoherentTensorHom B S hS P.R (τ i) (τ j) ≫
      (quasicoherentPullbackTensorIso B S hS P.source (Mn i) (Mn j)).inv ≫
      quasicoherentPullbackMap B S hS P.source (m i j))

/-- **Descended multiplications of associative multiplications are associative**: for a
presentation `X = U/R`, quasi-coherent modules `M_n` on the scheme of `U` with scheme transitions
and multiplications `m : M_i ⊗ M_j ⟶ M_{i+j}` compatible with the transitions, the descended
multiplications `D(M_i) ⊗ D(M_j) ⟶ D(M_{i+j})` of
`AlgebraicGeometry.Space.presentationDescendedMul` are associative as soon as the `m` are. -/
theorem presentationDescendedMul_assoc
    (hassoc : ∀ i j k, quasicoherentTensorHom B S hS P.U (m i j) (𝟙 (Mn k)) ≫ m (i + j) k =
      (quasicoherentAssociator B S hS P.U (Mn i) (Mn j) (Mn k)).hom ≫
        quasicoherentTensorHom B S hS P.U (𝟙 (Mn i)) (m j k) ≫ m i (j + k) ≫
        eqToHom (congrArg Mn (add_assoc i j k).symm))
    (i j k : ℤ) :
    (presentationDescendedMul P (τ i) (hc i) (hu i) (τ j) (hc j) (hu j)
        (τ (i + j)) (hc (i + j)) (hu (i + j)) (m i j) (hbt i j) (hbs i j) (hm i j)) ▷
            (presentationDescendedModule P (Mn k) (τ k) (hc k) (hu k)).obj ≫
      presentationDescendedMul P (τ (i + j)) (hc (i + j)) (hu (i + j)) (τ k) (hc k) (hu k)
        (τ (i + j + k)) (hc (i + j + k)) (hu (i + j + k)) (m (i + j) k) (hbt (i + j) k)
            (hbs (i + j) k) (hm (i + j) k) =
    (α_ (presentationDescendedModule P (Mn i) (τ i) (hc i) (hu i)).obj
        (presentationDescendedModule P (Mn j) (τ j) (hc j) (hu j)).obj
            (presentationDescendedModule P (Mn k) (τ k) (hc k) (hu k)).obj).hom ≫
      (presentationDescendedModule P (Mn i) (τ i) (hc i) (hu i)).obj ◁
          (presentationDescendedMul P (τ j) (hc j) (hu j) (τ k) (hc k) (hu k)
        (τ (j + k)) (hc (j + k)) (hu (j + k)) (m j k) (hbt j k) (hbs j k) (hm j k)) ≫
      presentationDescendedMul P (τ i) (hc i) (hu i) (τ (j + k)) (hc (j + k)) (hu (j + k))
        (τ (i + (j + k))) (hc (i + (j + k))) (hu (i + (j + k))) (m i (j + k)) (hbt i (j + k))
            (hbs i (j + k)) (hm i (j + k)) ≫
      eqToHom (congrArg (fun n => (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj)
          (add_assoc i j k).symm) := by
  have := fun n => isQuasicoherentOnSite_presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)
  have := isQuasicoherentOnSite_tensorObj B S hS X.obj X.property
      (presentationDescendedModule P (Mn i) (τ i) (hc i) (hu i)).obj
          (presentationDescendedModule P (Mn j) (τ j) (hc j) (hu j)).obj
  have := isQuasicoherentOnSite_tensorObj B S hS X.obj X.property
      ((presentationDescendedModule P (Mn i) (τ i) (hc i) (hu i)).obj ⊗
          (presentationDescendedModule P (Mn j) (τ j) (hc j) (hu j)).obj)
              (presentationDescendedModule P (Mn k) (τ k) (hc k) (hu k)).obj
  refine presentationAtlas_map_injective P ?_
  refine modulePullback_map_mul_assoc_of_chart (presentationAtlas P)
    (G := fun n => (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj)
    (fun n => presentationDescendedModuleChartIso P (Mn n) (τ n) (hc n) (hu n))
    (fun i j => presentationDescendedMul P (τ i) (hc i) (hu i) (τ j) (hc j) (hu j)
        (τ (i + j)) (hc (i + j)) (hu (i + j)) (m i j) (hbt i j) (hbs i j) (hm i j))
    (fun i j => representedTensorChartMul B S hS (m i j)) ?_ ?_ i j k
  · exact fun i j =>
      presentationDescendedMul_spec P _ _ _ _ _ _ _ _ _ (m i j) (hbt i j) (hbs i j) (hm i j)
  · exact fun i j k => representedTensorChartMul_assoc B S hS P.U m hassoc i j k

/-- **Descended multiplications of commutative multiplications are commutative**, the companion
of `AlgebraicGeometry.Space.presentationDescendedMul_assoc` for the symmetry constraints. -/
theorem presentationDescendedMul_comm
    (hcomm : ∀ i j, (quasicoherentBraiding B S hS P.U (Mn i) (Mn j)).hom ≫ m j i =
      m i j ≫ eqToHom (congrArg Mn (add_comm i j)))
    (i j : ℤ) :
    (β_ (presentationDescendedModule P (Mn i) (τ i) (hc i) (hu i)).obj
        (presentationDescendedModule P (Mn j) (τ j) (hc j) (hu j)).obj).hom ≫
            presentationDescendedMul P (τ j) (hc j) (hu j) (τ i) (hc i) (hu i)
        (τ (j + i)) (hc (j + i)) (hu (j + i)) (m j i) (hbt j i) (hbs j i) (hm j i) =
    presentationDescendedMul P (τ i) (hc i) (hu i) (τ j) (hc j) (hu j)
        (τ (i + j)) (hc (i + j)) (hu (i + j)) (m i j) (hbt i j) (hbs i j) (hm i j) ≫
      eqToHom (congrArg (fun n => (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj)
          (add_comm i j)) := by
  have := fun n => isQuasicoherentOnSite_presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)
  have := isQuasicoherentOnSite_tensorObj B S hS X.obj X.property
      (presentationDescendedModule P (Mn i) (τ i) (hc i) (hu i)).obj
          (presentationDescendedModule P (Mn j) (τ j) (hc j) (hu j)).obj
  refine presentationAtlas_map_injective P ?_
  refine modulePullback_map_mul_comm_of_chart (presentationAtlas P)
    (G := fun n => (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj)
    (fun n => presentationDescendedModuleChartIso P (Mn n) (τ n) (hc n) (hu n))
    (fun i j => presentationDescendedMul P (τ i) (hc i) (hu i) (τ j) (hc j) (hu j)
        (τ (i + j)) (hc (i + j)) (hu (i + j)) (m i j) (hbt i j) (hbs i j) (hm i j))
    (fun i j => representedTensorChartMul B S hS (m i j)) ?_ ?_ i j
  · exact fun i j =>
      presentationDescendedMul_spec P _ _ _ _ _ _ _ _ _ (m i j) (hbt i j) (hbs i j) (hm i j)
  · exact fun i j => representedTensorChartMul_comm B S hS P.U m hcomm i j

/-- **The descended unit of a left unit is a left unit**: for a morphism `ν : 𝒪_U ⟶ M_0` compatible
with the transitions and a left unit for the multiplications `m`, the descended unit
`𝒪_X ⟶ D(M_0)` of `AlgebraicGeometry.Space.presentationDescendedUnit` is a left unit for the
descended multiplications. -/
theorem presentationDescendedUnit_mul (ν : quasicoherentUnitObj B S hS P.U ⟶ Mn 0)
    (hbtu : RepresentedC3UnitCompat B S hS P.target)
    (hbsu : RepresentedC3UnitCompat B S hS P.source)
    (hmu : (quasicoherentPullbackUnitIso B S hS P.target).inv ≫
        quasicoherentPullbackMap B S hS P.target ν ≫ τ 0 =
      (quasicoherentPullbackUnitIso B S hS P.source).inv ≫
        quasicoherentPullbackMap B S hS P.source ν)
    (hone : ∀ n, quasicoherentTensorHom B S hS P.U ν (𝟙 (Mn n)) ≫ m 0 n =
      (quasicoherentLeftUnitor B S hS P.U (Mn n)).hom ≫ eqToHom (congrArg Mn (zero_add n).symm))
    (n : ℤ) :
    MonoidalCategoryStruct.whiskerRight (C := Modules.{u, u} B S hS X.obj X.property)
        (presentationDescendedUnit P (τ 0) (hc 0) (hu 0) ν hbtu hbsu hmu)
            (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj ≫
      presentationDescendedMul P (τ 0) (hc 0) (hu 0) (τ n) (hc n) (hu n)
        (τ (0 + n)) (hc (0 + n)) (hu (0 + n)) (m 0 n) (hbt 0 n) (hbs 0 n) (hm 0 n) =
    (λ_ (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj).hom ≫ eqToHom
        (congrArg (fun p => (presentationDescendedModule P (Mn p) (τ p) (hc p) (hu p)).obj)
            (zero_add n).symm) := by
  have := fun n => isQuasicoherentOnSite_presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)
  have := @isQuasicoherentOnSite_tensorObj B S hS X.obj X.property
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj
    (SheafOfModules.isQuasicoherentOnSite_unit _) inferInstance
  refine presentationAtlas_map_injective P ?_
  refine modulePullback_map_one_mul_of_chart (presentationAtlas P)
    (G := fun n => (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj)
    (fun n => presentationDescendedModuleChartIso P (Mn n) (τ n) (hc n) (hu n))
    (fun i j => presentationDescendedMul P (τ i) (hc i) (hu i) (τ j) (hc j) (hu j)
        (τ (i + j)) (hc (i + j)) (hu (i + j)) (m i j) (hbt i j) (hbs i j) (hm i j))
    (fun i j => representedTensorChartMul B S hS (m i j)) ?_
    (presentationDescendedUnit P (τ 0) (hc 0) (hu 0) ν hbtu hbsu hmu)
    (representedUnitChartHom B S hS ν) ?_ ?_ n
  · exact fun i j =>
      presentationDescendedMul_spec P _ _ _ _ _ _ _ _ _ (m i j) (hbt i j) (hbs i j) (hm i j)
  · exact presentationDescendedUnit_spec P (τ 0) (hc 0) (hu 0) ν hbtu hbsu hmu
  · exact fun n => representedTensorChartMul_one_mul B S hS P.U m ν hone n

/-- **The descended unit of a unit for a commutative multiplication is a right unit**: the
right unit law follows from the left unit law of
`AlgebraicGeometry.Space.presentationDescendedUnit_mul` and the commutativity of
`AlgebraicGeometry.Space.presentationDescendedMul_comm`. -/
theorem presentationDescendedMul_unit (ν : quasicoherentUnitObj B S hS P.U ⟶ Mn 0)
    (hbtu : RepresentedC3UnitCompat B S hS P.target)
    (hbsu : RepresentedC3UnitCompat B S hS P.source)
    (hmu : (quasicoherentPullbackUnitIso B S hS P.target).inv ≫
        quasicoherentPullbackMap B S hS P.target ν ≫ τ 0 =
      (quasicoherentPullbackUnitIso B S hS P.source).inv ≫
        quasicoherentPullbackMap B S hS P.source ν)
    (hone : ∀ n, quasicoherentTensorHom B S hS P.U ν (𝟙 (Mn n)) ≫ m 0 n =
      (quasicoherentLeftUnitor B S hS P.U (Mn n)).hom ≫ eqToHom (congrArg Mn (zero_add n).symm))
    (hcomm : ∀ i j, (quasicoherentBraiding B S hS P.U (Mn i) (Mn j)).hom ≫ m j i =
      m i j ≫ eqToHom (congrArg Mn (add_comm i j)))
    (n : ℤ) :
    MonoidalCategoryStruct.whiskerLeft (C := Modules.{u, u} B S hS X.obj X.property)
        (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj
        (presentationDescendedUnit P (τ 0) (hc 0) (hu 0) ν hbtu hbsu hmu) ≫
      presentationDescendedMul P (τ n) (hc n) (hu n) (τ 0) (hc 0) (hu 0)
        (τ (n + 0)) (hc (n + 0)) (hu (n + 0)) (m n 0) (hbt n 0) (hbs n 0) (hm n 0) =
    (ρ_ (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj).hom ≫ eqToHom
        (congrArg (fun p => (presentationDescendedModule P (Mn p) (τ p) (hc p) (hu p)).obj)
            (add_zero n).symm) :=
  mul_one_of_one_mul_of_comm
      (G := fun n => (presentationDescendedModule P (Mn n) (τ n) (hc n) (hu n)).obj)
    (fun i j => presentationDescendedMul P (τ i) (hc i) (hu i) (τ j) (hc j) (hu j)
      (τ (i + j)) (hc (i + j)) (hu (i + j)) (m i j) (hbt i j) (hbs i j) (hm i j))
    (presentationDescendedUnit P (τ 0) (hc 0) (hu 0) ν hbtu hbsu hmu)
    (fun n => presentationDescendedUnit_mul P τ hc hu m hbt hbs hm ν hbtu hbsu hmu hone n)
    (fun i j => presentationDescendedMul_comm P τ hc hu m hbt hbs hm hcomm i j) n

end PresentationLaws


namespace RelativeProjPoints

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P) {Mn : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : ∀ n, quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) (Mn n) ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) (Mn n))
  (hc : ∀ n, PresentationSchemeCocycle (d.spacePresentation Px hP) (Mn n) (τ n))
  (hu : ∀ n, PresentationSchemeUnit (d.spacePresentation Px hP) (Mn n) (τ n))
  (m : ∀ i j, quasicoherentTensorObj B S hS (d.fibre Px.U Px.toSpace) (Mn i) (Mn j) ⟶ Mn (i + j))
  (hbt : ∀ i j, RepresentedC3TensorCompat B S hS (d.spaceTarget Px hP) (Mn i) (Mn j))
  (hbs : ∀ i j, RepresentedC3TensorCompat B S hS (d.spaceSource Px hP) (Mn i) (Mn j))
  (hm : ∀ i j, d.TransitionMulCompat Px hP (τ i) (τ j) (τ (i + j)) (m i j))

/-- `AlgebraicGeometry.Space.presentationDescendedMul_assoc` on the presentation `P = P_U/P_R`,
with its data spelled through the base changes `U ×_X P`, `R ×_X P`. -/
theorem spacePresentationDescendedMul_assoc
    (hassoc : ∀ i j k, quasicoherentTensorHom B S hS (d.fibre Px.U Px.toSpace) (m i j)
        (𝟙 (Mn k)) ≫ m (i + j) k =
      (quasicoherentAssociator B S hS (d.fibre Px.U Px.toSpace) (Mn i) (Mn j) (Mn k)).hom ≫
        quasicoherentTensorHom B S hS (d.fibre Px.U Px.toSpace) (𝟙 (Mn i)) (m j k) ≫ m i (j + k) ≫
        eqToHom (congrArg Mn (add_assoc i j k).symm))
    (i j k : ℤ) :
    (d.spacePresentationDescendedMul Px hP (τ i) (τ j) (τ (i + j)) (m i j) (hc i) (hu i)
        (hc j) (hu j) (hc (i + j)) (hu (i + j)) (hbt i j) (hbs i j) (hm i j)) ▷
            (presentationDescendedModule (d.spacePresentation Px hP) (Mn k) (τ k) (hc k)
                (hu k)).obj ≫
      d.spacePresentationDescendedMul Px hP (τ (i + j)) (τ k) (τ (i + j + k)) (m (i + j) k)
          (hc (i + j)) (hu (i + j))
        (hc k) (hu k) (hc (i + j + k)) (hu (i + j + k)) (hbt (i + j) k) (hbs (i + j) k)
            (hm (i + j) k) =
    (α_ (presentationDescendedModule (d.spacePresentation Px hP) (Mn i) (τ i) (hc i) (hu i)).obj
        (presentationDescendedModule (d.spacePresentation Px hP) (Mn j) (τ j) (hc j) (hu j)).obj
            (presentationDescendedModule (d.spacePresentation Px hP) (Mn k) (τ k) (hc k)
                (hu k)).obj).hom ≫
      (presentationDescendedModule (d.spacePresentation Px hP) (Mn i) (τ i) (hc i) (hu i)).obj ◁
          (d.spacePresentationDescendedMul Px hP (τ j) (τ k) (τ (j + k)) (m j k) (hc j) (hu j)
        (hc k) (hu k) (hc (j + k)) (hu (j + k)) (hbt j k) (hbs j k) (hm j k)) ≫
      d.spacePresentationDescendedMul Px hP (τ i) (τ (j + k)) (τ (i + (j + k))) (m i (j + k))
          (hc i) (hu i)
        (hc (j + k)) (hu (j + k)) (hc (i + (j + k))) (hu (i + (j + k))) (hbt i (j + k))
            (hbs i (j + k)) (hm i (j + k)) ≫
      eqToHom (congrArg
          (fun n => (presentationDescendedModule (d.spacePresentation Px hP) (Mn n) (τ n) (hc n)
              (hu n)).obj) (add_assoc i j k).symm) :=
  presentationDescendedMul_assoc (d.spacePresentation Px hP) τ hc hu m hbt hbs
    (fun i j => d.spacePresentation_mul_transition Px hP _ _ _ _ (hm i j)) hassoc i j k

/-- `AlgebraicGeometry.Space.presentationDescendedMul_comm` on the presentation `P = P_U/P_R`,
with its data spelled through the base changes `U ×_X P`, `R ×_X P`. -/
theorem spacePresentationDescendedMul_comm
    (hcomm : ∀ i j, (quasicoherentBraiding B S hS (d.fibre Px.U Px.toSpace) (Mn i) (Mn j)).hom ≫
      m j i = m i j ≫ eqToHom (congrArg Mn (add_comm i j)))
    (i j : ℤ) :
    (β_ (presentationDescendedModule (d.spacePresentation Px hP) (Mn i) (τ i) (hc i) (hu i)).obj
        (presentationDescendedModule (d.spacePresentation Px hP) (Mn j) (τ j) (hc j)
            (hu j)).obj).hom ≫ d.spacePresentationDescendedMul Px hP (τ j) (τ i) (τ (j + i))
                (m j i) (hc j) (hu j)
        (hc i) (hu i) (hc (j + i)) (hu (j + i)) (hbt j i) (hbs j i) (hm j i) =
    d.spacePresentationDescendedMul Px hP (τ i) (τ j) (τ (i + j)) (m i j) (hc i) (hu i)
        (hc j) (hu j) (hc (i + j)) (hu (i + j)) (hbt i j) (hbs i j) (hm i j) ≫
      eqToHom (congrArg
          (fun n => (presentationDescendedModule (d.spacePresentation Px hP) (Mn n) (τ n) (hc n)
              (hu n)).obj) (add_comm i j)) :=
  presentationDescendedMul_comm (d.spacePresentation Px hP) τ hc hu m hbt hbs
    (fun i j => d.spacePresentation_mul_transition Px hP _ _ _ _ (hm i j)) hcomm i j

variable (ν : quasicoherentUnitObj B S hS (d.fibre Px.U Px.toSpace) ⟶ Mn 0)
  (hbtu : RepresentedC3UnitCompat B S hS (d.spaceTarget Px hP))
  (hbsu : RepresentedC3UnitCompat B S hS (d.spaceSource Px hP))
  (hmu : d.TransitionUnitCompat Px hP (τ 0) ν)
  (hone : ∀ n, quasicoherentTensorHom B S hS (d.fibre Px.U Px.toSpace) ν (𝟙 (Mn n)) ≫ m 0 n =
    (quasicoherentLeftUnitor B S hS (d.fibre Px.U Px.toSpace) (Mn n)).hom ≫
      eqToHom (congrArg Mn (zero_add n).symm))

include hone in
/-- `AlgebraicGeometry.Space.presentationDescendedUnit_mul` on the presentation `P = P_U/P_R`,
with its data spelled through the base changes `U ×_X P`, `R ×_X P`. -/
theorem spacePresentationDescendedUnit_mul (n : ℤ) :
    MonoidalCategoryStruct.whiskerRight (C := Modules.{u, u} B S hS P hP)
        (d.spacePresentationDescendedUnit Px hP (τ 0) ν (hc 0) (hu 0) hbtu hbsu hmu)
            (presentationDescendedModule (d.spacePresentation Px hP) (Mn n) (τ n) (hc n)
                (hu n)).obj ≫
      d.spacePresentationDescendedMul Px hP (τ 0) (τ n) (τ (0 + n)) (m 0 n) (hc 0) (hu 0)
        (hc n) (hu n) (hc (0 + n)) (hu (0 + n)) (hbt 0 n) (hbs 0 n) (hm 0 n) =
    (λ_ (presentationDescendedModule (d.spacePresentation Px hP) (Mn n) (τ n) (hc n)
        (hu n)).obj).hom ≫ eqToHom
            (congrArg (fun p =>
                (presentationDescendedModule (d.spacePresentation Px hP) (Mn p) (τ p) (hc p)
                    (hu p)).obj) (zero_add n).symm) :=
  presentationDescendedUnit_mul (d.spacePresentation Px hP) τ hc hu m hbt hbs
    (fun i j => d.spacePresentation_mul_transition Px hP _ _ _ _ (hm i j)) ν hbtu hbsu
    (d.spacePresentation_unit_transition Px hP _ _ hmu)
    hone n

include hone in
/-- `AlgebraicGeometry.Space.presentationDescendedMul_unit` on the presentation `P = P_U/P_R`,
with its data spelled through the base changes `U ×_X P`, `R ×_X P`. -/
theorem spacePresentationDescendedMul_unit
    (hcomm : ∀ i j, (quasicoherentBraiding B S hS (d.fibre Px.U Px.toSpace) (Mn i) (Mn j)).hom ≫
      m j i = m i j ≫ eqToHom (congrArg Mn (add_comm i j)))
    (n : ℤ) :
    MonoidalCategoryStruct.whiskerLeft (C := Modules.{u, u} B S hS P hP)
        (presentationDescendedModule (d.spacePresentation Px hP) (Mn n) (τ n) (hc n) (hu n)).obj
        (d.spacePresentationDescendedUnit Px hP (τ 0) ν (hc 0) (hu 0) hbtu hbsu hmu) ≫
      d.spacePresentationDescendedMul Px hP (τ n) (τ 0) (τ (n + 0)) (m n 0) (hc n) (hu n)
        (hc 0) (hu 0) (hc (n + 0)) (hu (n + 0)) (hbt n 0) (hbs n 0) (hm n 0) =
    (ρ_ (presentationDescendedModule (d.spacePresentation Px hP) (Mn n) (τ n) (hc n)
        (hu n)).obj).hom ≫ eqToHom
            (congrArg (fun p =>
                (presentationDescendedModule (d.spacePresentation Px hP) (Mn p) (τ p) (hc p)
                    (hu p)).obj) (add_zero n).symm) :=
  presentationDescendedMul_unit (d.spacePresentation Px hP) τ hc hu m hbt hbs
    (fun i j => d.spacePresentation_mul_transition Px hP _ _ _ _ (hm i j)) ν hbtu hbsu
    (d.spacePresentation_unit_transition Px hP _ _ hmu)
    hone hcomm n

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **The multiplication of the twists on the scheme of a base change is associative**, as an
equation of morphisms of quasi-coherent modules out of `(𝒪(i) ⊗ 𝒪(j)) ⊗ 𝒪(k)`. -/
theorem twistPieceMul_assoc (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (i j k : ℤ) :
    quasicoherentTensorHom s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
        (s.twistPieceMul V v i j) (𝟙 (s.twistPieceQcoh V v k)) ≫ s.twistPieceMul V v (i + j) k =
      (quasicoherentAssociator s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
          (s.twistPieceQcoh V v i) (s.twistPieceQcoh V v j) (s.twistPieceQcoh V v k)).hom ≫
        quasicoherentTensorHom s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
          (𝟙 (s.twistPieceQcoh V v i)) (s.twistPieceMul V v j k) ≫
        s.twistPieceMul V v i (j + k) ≫
        eqToHom (congrArg (s.twistPieceQcoh V v) (add_assoc i j k).symm) :=
  quasicoherentMul_assoc_of_eq s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
    (G := pbAlgS (s.toRelativeProj V v) (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v)))
    (hq := fun n => (s.twistPieceQcoh V v n).property)
    (funext fun _ => rfl) (fun i j => s.twistPieceMul V v i j) (fun _ _ => HEq.rfl) i j k

/-- **The multiplication of the twists on the scheme of a base change is commutative**, as an
equation of morphisms of quasi-coherent modules out of `𝒪(i) ⊗ 𝒪(j)`. -/
theorem twistPieceMul_comm (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (i j : ℤ) :
    (quasicoherentBraiding s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
        (s.twistPieceQcoh V v i) (s.twistPieceQcoh V v j)).hom ≫ s.twistPieceMul V v j i =
      s.twistPieceMul V v i j ≫ eqToHom (congrArg (s.twistPieceQcoh V v) (add_comm i j)) :=
  quasicoherentMul_comm_of_eq s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
    (G := pbAlgS (s.toRelativeProj V v) (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v)))
    (hq := fun n => (s.twistPieceQcoh V v n).property)
    (fun p q U x y => Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm_of_comm
      (s.toRelativeProj V v).toLRSHom.toShHom
      (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v))
      (fun a b W x' y' => (GluedTwistAlgebra.twistDataOfGradedAlgebra
        (s.shrink.pointAlgebra V v)).mul_comm a b W x' y') p q U x y)
    (funext fun _ => rfl) (fun i j => s.twistPieceMul V v i j) (fun _ _ => HEq.rfl) i j


/-- **The unit of the twists on the scheme of a base change is a left unit for their
multiplication**, as an equation of morphisms of quasi-coherent modules out of `𝒪 ⊗ 𝒪(n)`. -/
theorem twistPieceUnit_mul (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (n : ℤ) :
    quasicoherentTensorHom s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
        (s.twistPieceUnit V v) (𝟙 (s.twistPieceQcoh V v n)) ≫ s.twistPieceMul V v 0 n =
      (quasicoherentLeftUnitor s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
          (s.twistPieceQcoh V v n)).hom ≫
        eqToHom (congrArg (s.twistPieceQcoh V v) (zero_add n).symm) :=
  quasicoherentOne_mul_of_eq s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
    (G := pbAlgS (s.toRelativeProj V v) (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v)))
    (hq := fun n => (s.twistPieceQcoh V v n).property)
    (funext fun _ => rfl) (fun i j => s.twistPieceMul V v i j) (fun _ _ => HEq.rfl)
    (s.twistPieceUnit V v) HEq.rfl n


end RelativeProjSituation

end AlgebraicGeometry.Space

end
