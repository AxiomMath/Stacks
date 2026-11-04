module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Homology.MapBifunctorReg
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Total tensor complex and descent to the homotopy category

Part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery`:
the tensor bifunctor on complexes of `O`-modules, the
complex-level functors of Statements 1 and 2, the additivity of `Tot(F(G, -))`, its descent
`bifunctorPhi` through the homotopy quotient with its `CommShift` datum, and the cochain
transport `Ψcoch` used to build the mapping-cone isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

/-- Tensoring presheaves of modules over a presheaf of commutative rings is additive
(bilinear on morphisms) in each variable: the tensor product, the whiskerings and the
addition of morphisms are all computed objectwise in `ModuleCat (R₀.obj X)`, which is
`MonoidalPreadditive`. -/
instance presheafOfModules_monoidalPreadditive {C : Type*} [Category C]
    (R₀ : Cᵒᵖ ⥤ CommRingCat) :
    MonoidalPreadditive (PresheafOfModules (R₀ ⋙ forget₂ CommRingCat RingCat)) where
  whiskerLeft_zero := by
    intros
    ext1 X
    simp only [PresheafOfModules.whiskerLeft_app, PresheafOfModules.zero_app,
      MonoidalPreadditive.whiskerLeft_zero]
    rfl
  zero_whiskerRight := by
    intros
    ext1 X
    simp only [PresheafOfModules.whiskerRight_app, PresheafOfModules.zero_app,
      MonoidalPreadditive.zero_whiskerRight]
    rfl
  whiskerLeft_add f g := by
    ext1 X
    simp only [PresheafOfModules.whiskerLeft_app, PresheafOfModules.add_app,
      MonoidalPreadditive.whiskerLeft_add]
    rfl
  add_whiskerRight f g := by
    ext1 X
    simp only [PresheafOfModules.whiskerRight_app, PresheafOfModules.add_app,
      MonoidalPreadditive.add_whiskerRight]
    rfl

namespace Stacks.SheafOfModules.Tensor

-- Background and context.
-- `(C, O)` is a ringed site; here `O = R` is a sheaf of *commutative* rings.
-- `Mod(O)` is the abelian category `SheafOfModules (ringSheaf R)` of sheaves of
-- `O`-modules; it has countable direct sums.
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

-- Main Definition(s)

variable [HasBinaryBiproducts (SheafOfModules (ringSheaf R))]

/-- **The total tensor complex `Tot(K₁^• ⊗_O K₂^•)` exists.**  Its degree `n` part is the
coproduct of `K₁^p ⊗_O K₂^q` over the pairs with `p + q = n`, a coproduct indexed by a small
type, and `Mod(O)` has all small colimits because presheaves of modules do and sheafification
is a left adjoint. -/
instance hasMapBifunctor_sheafTensor
    (K₁ K₂ : CochainComplex (SheafOfModules (ringSheaf R)) ℤ) :
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (sheafTensor R) (ComplexShape.up ℤ) :=
  inferInstance

/-- **Definitions 3 and 4.**  `Tot(- ⊗_O -)`, the bifunctor on cochain complexes
sending `(K₁^•, K₂^•)` to the total complex `Tot(K₁^• ⊗_O K₂^•)` of the tensor
double complex (Koszul sign convention).  This is `Functor.map₂HomologicalComplexReg`
applied to `sheafTensor`: Mathlib's `Functor.map₂HomologicalComplex`, with objects and
morphisms whose kernel reducibility hints are regular, so that the kernel compares two
spellings of a value argument by argument instead of evaluating `sheafTensor`.  The instance
arguments are the additivity of `⊗_O` in each variable and the countable direct sums needed to
form the total complexes; all three are discharged by `sheafTensor_additive`,
`sheafTensor_obj_additive` and `hasMapBifunctor_sheafTensor` above. -/
def tensorComplex
    [(sheafTensor.{_, _, _, w, w} R).Additive]
    [∀ X, ((sheafTensor.{_, _, _, w, w} R).obj X).Additive]
    [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ)),
        K₁.HasMapBifunctorReg K₂ (sheafTensor R) (ComplexShape.up ℤ)] :
    HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) ⥤
      HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) ⥤
        HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) :=
  (sheafTensor R).map₂HomologicalComplexReg (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)

/-- The complex-level functor of Statement 1: for a fixed complex `G^•`, the
functor `F^• ↦ Tot(G^• ⊗_O F^•)` on `Comp(Mod(O))` (the fixed complex `G^•` is
the LEFT tensor factor). -/
def leftTensorComplex
    [(sheafTensor.{_, _, _, w, w} R).Additive]
    [∀ X, ((sheafTensor.{_, _, _, w, w} R).obj X).Additive]
    [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ)),
        K₁.HasMapBifunctorReg K₂ (sheafTensor R) (ComplexShape.up ℤ)]
    (G : HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ)) :
    HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) ⥤
      HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) :=
  (tensorComplex R).obj G

/-- The complex-level functor of Statement 2: for a fixed complex `G^•`, the
functor `F^• ↦ Tot(F^• ⊗_O G^•)` on `Comp(Mod(O))` (the fixed complex `G^•` is
the RIGHT tensor factor). -/
def rightTensorComplex
    [(sheafTensor.{_, _, _, w, w} R).Additive]
    [∀ X, ((sheafTensor.{_, _, _, w, w} R).obj X).Additive]
    [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ)),
        K₁.HasMapBifunctorReg K₂ (sheafTensor R) (ComplexShape.up ℤ)]
    (G : HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ)) :
    HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) ⥤
      HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) :=
  (tensorComplex R).flip.obj G

/-- The canonical quotient functor `Comp(Mod(O)) ⥤ K(Mod(O))` onto the homotopy
category. -/
def quotF :
    HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ)

/-!
## General reduction machinery (tag 0G6E)

The Stacks proof reduces both statements to the general fact (Derived Categories,
Remark 13.10.9 / tag 0G6E): for an additive bifunctor `F : A ⥤ B ⥤ D` (`D` with
the countable direct sums needed for the total complexes), fixing one complex
variable `G^•` and taking `Tot(F(-, -))` of the double complex descends to an
exact functor of homotopy categories.

We package this once and for all, separately for the case where the fixed complex
is the LEFT factor (`bifunctorPhi`, used for Statement 1) and the RIGHT factor
(`bifunctorPhiR`, used for Statement 2).  The construction:

1. The complex-level functor `Tot(F(G, -)) = (F.map₂HomologicalComplex …).obj G`
   is additive (`map₂HomologicalComplex_obj_additive`) — proved by hand because
   Mathlib provides no instance.
2. It descends through the homotopy quotient because it is homotopy-invariant
   (`HomologicalComplex.mapBifunctorMapHomotopy₂` for the left case,
   `…Homotopy₁` for the right): `bifunctorPhi := Quotient.lift …`.  The lift
   isomorphism `bifunctorPhiFactors` is the well-definedness witness `ξ`'s sibling
   `quotF ⋙ Φ ≅ Tot(F(G, -)) ⋙ quotF`.
3. `Φ` inherits additivity from the quotient being full and essentially
   surjective (`Functor.additive_of_full_essSurj_comp`).
4. `Φ` inherits a `CommShift ℤ` datum `ξ` from the existing complex-level
   `CommShift` (the Koszul-sign isomorphism of tag 0FLG) via
   `Quotient.liftCommShift`.
5. `Φ` is triangulated — the genuine mathematical content (see
   `bifunctorPhi_isTriangulated`).
-/

namespace Reduction

attribute [local implicit_reducible] Functor.map₂HomologicalComplex

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [Preadditive D]
  [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D]

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- `Tot(F(G, -)) = (F.map₂HomologicalComplex …).obj G` is additive in `-`.
Bilinearity of `F` in the second variable transports through `mapBifunctorMap`;
proved by extensionality on the total-complex summands. -/
lemma map₂HomologicalComplex_obj_additive
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ)) :
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj G).Additive := by
  constructor
  intro K L f g
  apply HomologicalComplex.hom_ext
  intro j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  show G.ιMapBifunctor K F (ComplexShape.up ℤ) i₁ i₂ j h ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 G) (f + g) F (ComplexShape.up ℤ)).f j
    = G.ιMapBifunctor K F (ComplexShape.up ℤ) i₁ i₂ j h ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 G) f F (ComplexShape.up ℤ)
        + HomologicalComplex.mapBifunctorMap (𝟙 G) g F (ComplexShape.up ℤ)).f j
  rw [HomologicalComplex.add_f_apply, Preadditive.comp_add,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.add_f_apply,
    Functor.map_add]
  simp only [Preadditive.comp_add, Preadditive.add_comp]

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- Right-factor variant of `map₂HomologicalComplex_obj_additive`:
`Tot(F(-, G)) = (F.map₂HomologicalComplex …).flip.obj G` is additive in `-`. -/
lemma map₂HomologicalComplex_flip_obj_additive
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) :
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).flip.obj G).Additive := by
  constructor
  intro K L f g
  apply HomologicalComplex.hom_ext
  intro j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  show K.ιMapBifunctor G F (ComplexShape.up ℤ) i₁ i₂ j h ≫
      (HomologicalComplex.mapBifunctorMap (f + g) (𝟙 G) F (ComplexShape.up ℤ)).f j
    = K.ιMapBifunctor G F (ComplexShape.up ℤ) i₁ i₂ j h ≫
      (HomologicalComplex.mapBifunctorMap f (𝟙 G) F (ComplexShape.up ℤ)
        + HomologicalComplex.mapBifunctorMap g (𝟙 G) F (ComplexShape.up ℤ)).f j
  rw [HomologicalComplex.add_f_apply, Preadditive.comp_add,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.add_f_apply,
    Functor.map_add]
  simp only [NatTrans.app_add, Preadditive.add_comp]

/-- **Left-factor case.**  The descended functor `Φ : K(B) ⥤ K(D)` lifting
`F^• ↦ Tot(F(G, F^•))`.  Homotopy-invariance (`mapBifunctorMapHomotopy₂`) makes
the descent well defined on homotopy classes. -/
noncomputable def bifunctorPhi
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ)) :
    HomotopyCategory B (ComplexShape.up ℤ) ⥤ HomotopyCategory D (ComplexShape.up ℤ) :=
  haveI := map₂HomologicalComplex_obj_additive F G
  CategoryTheory.Quotient.lift (homotopic B (ComplexShape.up ℤ))
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G ⋙ HomotopyCategory.quotient D (ComplexShape.up ℤ))
    (by
      rintro x y f₁ f₂ ⟨hfg⟩
      dsimp
      rw [HomotopyCategory.eq_of_homotopy]
      exact HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 G) hfg F (ComplexShape.up ℤ))

/-- The lift isomorphism `quotient ⋙ Φ ≅ Tot(F(G, -)) ⋙ quotient` (left case). -/
noncomputable def bifunctorPhiFactors
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ)) :
    HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ bifunctorPhi F G ≅
      (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G ⋙ HomotopyCategory.quotient D (ComplexShape.up ℤ) :=
  haveI := map₂HomologicalComplex_obj_additive F G
  Quotient.lift.isLift _ _ _

/-- `Φ` (left case) is additive, since the quotient functor is full and
essentially surjective and `quotient ⋙ Φ` is additive. -/
instance bifunctorPhi_additive
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ)) :
    (bifunctorPhi F G).Additive := by
  have := map₂HomologicalComplex_obj_additive F G
  have : (HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ bifunctorPhi F G).Additive :=
    Functor.additive_of_iso (bifunctorPhiFactors F G).symm
  exact Functor.additive_of_full_essSurj_comp
    (HomotopyCategory.quotient B (ComplexShape.up ℤ)) _

/-- The functorial commutation-with-shift datum `ξ` for `Φ` (left case): the
descent of the complex-level `CommShift ℤ` (the Koszul-sign isomorphism of tag
0FLG) along the homotopy quotient. -/
@[reducible]
noncomputable def bifunctorXi
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ)) :
    (bifunctorPhi F G).CommShift ℤ :=
  haveI := map₂HomologicalComplex_obj_additive F G
  Quotient.liftCommShift _ _ _ _

/- **C1 (cone-object iso).**  The complex-level bifunctor mapping-cone comparison:
for `Ψ := (F.map₂HomologicalComplex …).obj G = Tot(F(G,-))`,
`Ψ.obj (mappingCone φ) ≅ mappingCone (Ψ.map φ)`.

This is the genuine kernel.  Mathlib's `CochainComplex.mappingCone.mapHomologicalComplexIso`
builds the analogue for `Φ.mapHomologicalComplex` from the degreewise
`mapHomologicalComplexXIso'` + the cochain transport `Cochain.map`
(`z ↦ Cochain.mk (fun p q h => Φ.map (z.v p q h))`).  Here `Ψ` is NOT degreewise on
`B`, but it IS the total complex of the degreewise bifunctor `F(G^p, (-)^q)`, so the
transport must be rebuilt through the `mapBifunctorMap`/`ιMapBifunctor` API:
on the `(p,q)` total-complex summand, a cochain component `z.v : (cone φ)^q → ?`
transports as `F(G^p, z.v)`.  Build:
  (a) the degreewise X-iso `(Ψ.obj (cone φ)).X n ≅ (cone (Ψ.map φ)).X n` from
      additivity of `F(G^p,-)` (biproduct preservation) + the total-complex
      decomposition, mirroring `mapHomologicalComplexXIso'`;
  (b) check it is a chain map (differential compatibility — the off-diagonal `φ`
      entry of the cone differential maps to `Ψ.map φ`, the diagonal `-d_K`/`d_L`
      entries to those of `cone (Ψ.map φ)`), assembling the object iso.
DEPENDENCY: no Mathlib support (this is the new API).

FORMAL SKETCH (this step).  The construction mirrors the single-variable model
`CochainComplex.mappingCone.mapHomologicalComplexIso`, but with the cochain
transport `Cochain.map` (which exists only for `Φ.mapHomologicalComplex`)
REPLACED by its bifunctor analogue `Ψcoch` below.  We then assemble the iso from
`mappingCone.lift`/`mappingCone.desc`, exactly as the model does, using the
algebra lemmas `Ψcoch_v`, `Ψcoch_ofHom`, `Ψcoch_comp`, `Ψcoch_δ` (the bifunctor
analogues of `Cochain.map_v`, the `ofHom` compatibility, `Cochain.map_comp`, and
`δ_map`).  Decomposed AND-style into those five helper sorries (C1a–C1f). -/

/-- **C1a (the bifunctor cochain transport — the new primitive).**  Bifunctor
analogue of `CochainComplex.HomComplex.Cochain.map`: transport a cochain
`z : Cochain X Y n` of `B` through `Ψ = Tot(F(G,-))` to a cochain
`Cochain (Ψ X) (Ψ Y) n` of `D`, degreewise on the total-complex summands via
`mapBifunctorDesc`/`ιMapBifunctor`.  (Verified to type-check by a closer pass.) -/
noncomputable def Ψcoch
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {X Y : CochainComplex B ℤ} {n : ℤ}
    (z : CochainComplex.HomComplex.Cochain X Y n) :
    CochainComplex.HomComplex.Cochain
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G).obj X)
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G).obj Y) n :=
  CochainComplex.HomComplex.Cochain.mk fun a a' h =>
    G.mapBifunctorDesc (K₂ := X) (c := ComplexShape.up ℤ) fun p q hpq =>
      (n * p).negOnePow •
        ((F.obj (G.X p)).map (z.v q (q + n) (by omega)) ≫
          G.ιMapBifunctor Y F (ComplexShape.up ℤ) p (q + n) a'
            (by have : p + q = a := hpq; change p + (q + n) = a'; omega))

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- **C1b.**  Degreewise value of `Ψcoch` (mirror `Cochain.map_v`): on the
`(p,q)` total-complex summand, `Ψcoch z` is `F(G^p, z.v …)`.  Proof via
`ι_mapBifunctorDesc`. -/
lemma Ψcoch_v
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {X Y : CochainComplex B ℤ} {n : ℤ}
    (z : CochainComplex.HomComplex.Cochain X Y n) (a a' : ℤ) (h : a + n = a')
    (p q : ℤ) (hpq : p + q = a) :
    G.ιMapBifunctor X F (ComplexShape.up ℤ) p q a hpq ≫ (Ψcoch F G z).v a a' h =
      (n * p).negOnePow •
        ((F.obj (G.X p)).map (z.v q (q + n) (by omega)) ≫
          G.ιMapBifunctor Y F (ComplexShape.up ℤ) p (q + n) a'
            (by change p + (q + n) = a'; omega)) := by
  simp only [Ψcoch, CochainComplex.HomComplex.Cochain.mk_v]
  rw [G.ι_mapBifunctorDesc]

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- **C1c.**  `Ψcoch` of (the cochain of) a chain map `f : X ⟶ Y` is the cochain
of `Ψ.map f` (mirror the `Cochain.ofHom` compatibility of `Cochain.map`). -/
lemma Ψcoch_ofHom
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {X Y : CochainComplex B ℤ} (f : X ⟶ Y) :
    Ψcoch F G (CochainComplex.HomComplex.Cochain.ofHom f) =
      CochainComplex.HomComplex.Cochain.ofHom
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj G).map f) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro a a' h
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpq2 : p + q = a := hpq
  -- LHS
  rw [Ψcoch_v F G (CochainComplex.HomComplex.Cochain.ofHom f) a a' h p q hpq2,
    zero_mul, Int.negOnePow_zero, one_smul]
  -- Normalise the index `q + 0` to `q` on the LHS cochain value and ι, then `ofHom_v`.
  have hLHS : (F.obj (G.X p)).map
        ((CochainComplex.HomComplex.Cochain.ofHom f).v q (q + 0) (by omega)) ≫
        G.ιMapBifunctor Y F (ComplexShape.up ℤ) p (q + 0) a' (by change p + (q + 0) = a'; omega)
      = (F.obj (G.X p)).map (f.f q) ≫
        G.ιMapBifunctor Y F (ComplexShape.up ℤ) p q a' (by omega) := by
    have key : ∀ (s : ℤ) (hs : q = s) (hv : q + 0 = s) (hι : (ComplexShape.up ℤ).π
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, s) = a'),
        (F.obj (G.X p)).map ((CochainComplex.HomComplex.Cochain.ofHom f).v q s hv) ≫
            G.ιMapBifunctor Y F (ComplexShape.up ℤ) p s a' hι
          = (F.obj (G.X p)).map (f.f q) ≫
            G.ιMapBifunctor Y F (ComplexShape.up ℤ) p q a' (by omega) := by
      intro s hs hv hι
      subst hs
      rw [CochainComplex.HomComplex.Cochain.ofHom_v]
    exact key (q + 0) (by omega) rfl (by change p + (q + 0) = a'; omega)
  rw [hLHS]
  -- RHS: normalise `a'` to `a` and apply `ofHom_v`, then push ι through `mapBifunctorMap`.
  have hRHS : G.ιMapBifunctor X F (ComplexShape.up ℤ) p q a hpq ≫
        (CochainComplex.HomComplex.Cochain.ofHom
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj G).map f)).v a a' h
      = (F.obj (G.X p)).map (f.f q) ≫
        G.ιMapBifunctor Y F (ComplexShape.up ℤ) p q a' (by omega) := by
    have key : ∀ (b : ℤ) (hb : a = b) (hv : a + 0 = b) (hι : (ComplexShape.up ℤ).π
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = a),
        G.ιMapBifunctor X F (ComplexShape.up ℤ) p q a hι ≫
          (CochainComplex.HomComplex.Cochain.ofHom
            (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).obj G).map f)).v a b hv
          = (F.obj (G.X p)).map (f.f q) ≫
            G.ιMapBifunctor Y F (ComplexShape.up ℤ) p q b (by omega) := by
      intro b hb hv hι
      subst hb
      rw [CochainComplex.HomComplex.Cochain.ofHom_v,
        Functor.map₂HomologicalComplex_obj_map,
        HomologicalComplex.ι_mapBifunctorMap]
      simp
    exact key a' (by omega) h hpq
  rw [hRHS]

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- **C1d.**  `Ψcoch` is multiplicative for cochain composition (mirror
`Cochain.map_comp`), since `F(G^p,-)` is a functor (preserves composition).
SANITY CHECK PASSED: signs match via `(n₁+n₂)*p = n₁*p+n₂*p` (`Int.negOnePow_add`),
`Cochain.comp_v` introduces no extra sign, G-index `p` preserved across composition. -/
lemma Ψcoch_comp
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {X Y Z : CochainComplex B ℤ} {n₁ n₂ n₁₂ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain X Y n₁)
    (z₂ : CochainComplex.HomComplex.Cochain Y Z n₂) (h : n₁ + n₂ = n₁₂) :
    Ψcoch F G (z₁.comp z₂ h) = (Ψcoch F G z₁).comp (Ψcoch F G z₂) h := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro a a' h'
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpq2 : p + q = a := hpq
  -- LHS
  rw [Ψcoch_v F G (z₁.comp z₂ h) a a' h' p q hpq2,
    CochainComplex.HomComplex.Cochain.comp_v z₁ z₂ h q (q + n₁) (q + n₁₂)
      rfl (by omega),
    Functor.map_comp]
  -- RHS
  rw [CochainComplex.HomComplex.Cochain.comp_v (Ψcoch F G z₁) (Ψcoch F G z₂) h
      a (a + n₁) a' rfl (by omega),
    ← Category.assoc,
    Ψcoch_v F G z₁ a (a + n₁) rfl p q hpq2,
    Linear.units_smul_comp,
    Category.assoc ((F.obj (G.X p)).map (z₁.v q (q + n₁) (by omega)))
      (G.ιMapBifunctor Y F (ComplexShape.up ℤ) p (q + n₁) (a + n₁) (by simp; omega))
      ((Ψcoch F G z₂).v (a + n₁) a' (by omega)),
    Ψcoch_v F G z₂ (a + n₁) a' (by omega) p (q + n₁) (by omega),
    Linear.comp_units_smul, smul_smul]
  -- Reconcile signs and the intermediate index `q + n₁ + n₂ = q + n₁₂`.
  have hsign : (n₁ * p).negOnePow * (n₂ * p).negOnePow = (n₁₂ * p).negOnePow := by
    rw [← Int.negOnePow_add]; congr 1; rw [← h]; ring
  have hbridge : (F.obj (G.X p)).map (z₂.v (q + n₁) (q + n₁ + n₂) (by omega)) ≫
        G.ιMapBifunctor Z F (ComplexShape.up ℤ) p (q + n₁ + n₂) a' (by simp; omega)
      = (F.obj (G.X p)).map (z₂.v (q + n₁) (q + n₁₂) (by omega)) ≫
        G.ιMapBifunctor Z F (ComplexShape.up ℤ) p (q + n₁₂) a' (by simp; omega) := by
    have key : ∀ (r : ℤ) (hr : (q + n₁) + n₂ = r) (hr' : (ComplexShape.up ℤ).π
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, r) = a'),
        (F.obj (G.X p)).map (z₂.v (q + n₁) r hr) ≫
            G.ιMapBifunctor Z F (ComplexShape.up ℤ) p r a' hr'
          = (F.obj (G.X p)).map (z₂.v (q + n₁) ((q + n₁) + n₂) rfl) ≫
            G.ιMapBifunctor Z F (ComplexShape.up ℤ) p ((q + n₁) + n₂) a' (by simp; omega) := by
      intro r hr hr'
      subst hr
      rfl
    exact (key (q + n₁ + n₂) rfl (by simp; omega)).trans
      (key (q + n₁₂) (by omega) (by simp; omega)).symm
  rw [hsign, hbridge, ← Category.assoc]

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- **C1e (the one nontrivial algebra fact).**  `Ψcoch` commutes with the
cochain differential `δ` (mirror `δ_map`).  The `G`-side `d₁` contribution of the
total differential cancels because the Koszul sign `(-1)^{n·p}` carried by `Ψcoch`
satisfies `σ(p,n) + (-1)^m σ(p+1,n) = 0` (with `m = n+1`); only the `d₂` part
(matching `δ` in `B`, transported by `F(G^p,-)`, with the same sign since the
`G`-index `p` is unchanged) survives.
SANITY CHECK PASSED: the sign-free statement was REFUTED for even `m`; the sign
`(-1)^{n·p}` on `Ψcoch` was derived precisely to make this identity hold for all
`n m`. -/
lemma Ψcoch_δ
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {X Y : CochainComplex B ℤ} (n m : ℤ)
    (z : CochainComplex.HomComplex.Cochain X Y n) :
    CochainComplex.HomComplex.δ n m (Ψcoch F G z) =
      Ψcoch F G (CochainComplex.HomComplex.δ n m z) := by
  by_cases hnm : n + 1 = m
  · apply CochainComplex.HomComplex.Cochain.ext
    intro a a' h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq2 : p + q = a := hpq
    subst hnm
    -- Helper: decompose `ι ≫ d` of the total complex into the two Koszul pieces.
    have hd : ∀ (W : CochainComplex B ℤ) (p₀ q₀ p₀' q₀' j j' : ℤ) (hjj : p₀ + q₀ = j)
        (hjj' : j + 1 = j') (hp : p₀ + 1 = p₀') (hq : q₀ + 1 = q₀'),
        G.ιMapBifunctor W F (ComplexShape.up ℤ) p₀ q₀ j hjj ≫
          (G.mapBifunctor W F (ComplexShape.up ℤ)).d j j'
        = (F.map (G.d p₀ p₀')).app (W.X q₀) ≫
            G.ιMapBifunctor W F (ComplexShape.up ℤ) p₀' q₀ j' (by simp; omega)
          + p₀.negOnePow • ((F.obj (G.X p₀)).map (W.d q₀ q₀') ≫
            G.ιMapBifunctor W F (ComplexShape.up ℤ) p₀ q₀' j' (by simp; omega)) := by
      intro W p₀ q₀ p₀' q₀' j j' hjj hjj' hp hq
      subst hp hq
      rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
        HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
        HomologicalComplex.mapBifunctor.d₁_eq G W F (ComplexShape.up ℤ) (i₁ := p₀)
          (i₁' := p₀ + 1) (by simp) q₀ j' (by simp; omega),
        HomologicalComplex.mapBifunctor.d₂_eq G W F (ComplexShape.up ℤ) p₀ (i₂ := q₀)
          (i₂' := q₀ + 1) (by simp) j' (by simp; omega),
        show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p₀, q₀) = 1 from rfl,
        show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p₀, q₀)
            = p₀.negOnePow from by rw [← ComplexShape.ε_up_ℤ p₀]; rfl, one_smul]
    rw [CochainComplex.HomComplex.δ_v n (n + 1) rfl _ a a' h (a' - 1) (a + 1)
        (by ring) (by ring)]
    rw [Preadditive.comp_add, Linear.comp_units_smul]
    -- Term 1: ι_X ≫ (Ψcoch z).v a (a'-1) ≫ d
    rw [← Category.assoc, Ψcoch_v F G z a (a' - 1) (by omega) p q hpq2,
      Linear.units_smul_comp, Category.assoc,
      show (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj G).obj Y).d (a' - 1) a'
        = (G.mapBifunctor Y F (ComplexShape.up ℤ)).d (a' - 1) a' from rfl,
      hd Y p (q + n) (p + 1) (q + (n + 1)) (a' - 1) a' (by omega) (by omega) rfl (by ring)]
    -- Term 2: ι_X ≫ d ≫ (Ψcoch z).v (a+1) a'
    rw [show (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj G).obj X).d a (a + 1)
        = (G.mapBifunctor X F (ComplexShape.up ℤ)).d a (a + 1) from rfl,
      ← Category.assoc, hd X p q (p + 1) (q + 1) a (a + 1) hpq2 rfl rfl rfl,
      Preadditive.add_comp,
      Category.assoc,
      Ψcoch_v F G z (a + 1) a' (by omega) (p + 1) q (by omega),
      Linear.comp_units_smul,
      Linear.units_smul_comp, Category.assoc,
      Ψcoch_v F G z (a + 1) a' (by omega) p (q + 1) (by omega)]
    -- RHS expansion.
    rw [Ψcoch_v F G (CochainComplex.HomComplex.δ n (n + 1) z) a a' h p q hpq2,
      CochainComplex.HomComplex.δ_v n (n + 1) rfl z q (q + (n + 1)) (by ring)
        (q + n) (q + 1) (by ring) (by ring),
      Functor.map_add, Preadditive.add_comp, Functor.map_units_smul,
      Linear.units_smul_comp]
    -- Match terms.  Use functoriality to merge the composite F.map's on the RHS,
    -- and naturality of `F.map (G.d p (p+1))` to align the two `d₁` (G-side) terms,
    -- which then cancel by the Koszul sign identity.
    rw [Functor.map_comp, Functor.map_comp,
      ← Category.assoc ((F.map (G.d p (p + 1))).app (X.X q))
        ((F.obj (G.X (p + 1))).map (z.v q (q + n) (by omega))),
      ← (F.map (G.d p (p + 1))).naturality (z.v q (q + n) (by omega))]
    -- Normalise the remaining index `q + 1 + n` to the common value `q + (n + 1)`.
    -- Distribute the outer `(n+1).negOnePow` scalar and pull all scalars to the front.
    simp only [smul_add, Preadditive.comp_add, Category.assoc,
      Linear.comp_units_smul, smul_smul]
    -- Sign facts.
    have hL2 : (n * p).negOnePow * p.negOnePow = ((n + 1) * p).negOnePow := by
      rw [show (n + 1) * p = n * p + p by ring, Int.negOnePow_add]
    have hL4 : (n + 1).negOnePow * (p.negOnePow * (n * p).negOnePow)
        = ((n + 1) * p).negOnePow * (n + 1).negOnePow := by
      rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]; congr 1; ring
    have hL13 : (n + 1).negOnePow * (n * (p + 1)).negOnePow = - (n * p).negOnePow := by
      rw [← Int.negOnePow_add, show (n + 1) + n * (p + 1) = (n * p) + (2 * n + 1) by ring,
        Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_two_mul]
      simp
    -- The two `d₁` (G-side) terms (sharing one morphism) cancel via `hL13`; the
    -- remaining `d₂` terms match the RHS via `hL2`, `hL4`, after bridging the index.
    rw [hL2, hL4, hL13, Units.neg_smul]
    -- Bridge the index `q + 1 + n` to `q + (n + 1)` in the surviving `d₂` term.
    have key : ∀ (r : ℤ) (hr : (q + 1) + n = r) (hr' : p + r = a'),
        (F.obj (G.X p)).map (z.v (q + 1) r hr) ≫
            G.ιMapBifunctor Y F (ComplexShape.up ℤ) p r a' hr'
          = (F.obj (G.X p)).map (z.v (q + 1) ((q + 1) + n) rfl) ≫
            G.ιMapBifunctor Y F (ComplexShape.up ℤ) p ((q + 1) + n) a'
              (by change p + ((q + 1) + n) = a'; omega) := by
      intro r hr hr'
      subst hr
      rfl
    have ebridge : (F.obj (G.X p)).map (z.v (q + 1) (q + 1 + n) (by omega)) ≫
          G.ιMapBifunctor Y F (ComplexShape.up ℤ) p (q + 1 + n) a'
            (by change p + (q + 1 + n) = a'; omega)
        = (F.obj (G.X p)).map (z.v (q + 1) (q + (n + 1)) (by omega)) ≫
          G.ιMapBifunctor Y F (ComplexShape.up ℤ) p (q + (n + 1)) a'
            (by change p + (q + (n + 1)) = a'; omega) :=
      (key (q + 1 + n) rfl (by show p + (q + 1 + n) = a'; omega)).trans
        (key (q + (n + 1)) (by ring) (by show p + (q + (n + 1)) = a'; omega)).symm
    rw [ebridge]
    abel
  · rw [CochainComplex.HomComplex.δ_shape n m hnm,
      CochainComplex.HomComplex.δ_shape n m hnm]
    apply CochainComplex.HomComplex.Cochain.ext
    intro a a' h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [Ψcoch_v]
    simp

end Reduction

end Stacks.SheafOfModules.Tensor

end
