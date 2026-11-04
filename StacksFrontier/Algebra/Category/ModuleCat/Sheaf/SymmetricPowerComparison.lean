module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.HomogeneousProdLeft
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01CG: the symmetric power of a sheaf of modules is a sheafification

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `M` a sheaf of modules over
the underlying sheaf of rings. Stacks Tag 01CG says that the degree-`n` symmetric power `Symⁿ M`
is the **sheafification** of the presheaf of sectionwise symmetric powers

`X ↦ Symⁿ_{O♯(X)}(M(X))`,

the comparison being the map that multiplies out products of degree-one generators.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification` builds that presheaf
(`PresheafOfModules.symPow`) and the comparison morphism
(`SheafOfModules.GradedAlgebra.symPowCmp`) and proves the two families of equations that
characterize them on products of degree-one generators. What was missing, and is proved here, is
the sheafification assertion itself: the comparison morphism becomes an isomorphism after
sheafifying. `SheafOfModules.symmetricPower_isSheafification` assembles the three assertions into
the single statement Tag 01CG makes, and carries the tag.

## Main definitions

* `SheafOfModules.sheafifySectionsIso`: sheafifying the underlying presheaf of modules of a sheaf
  of modules returns it — the counit of the sheafification adjunction along the identity of the
  ring sheaf, which is an isomorphism.
* `SheafOfModules.symmetricDesc`: the unital homomorphism of sheaves of graded algebras from the
  sheafified sectionwise symmetric algebra of the sections of `M` to any symmetric algebra of `M`,
  and `SheafOfModules.symmetricPieceIso` its degreewise isomorphism.

## Main results

* `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.comp_iso`: **the symmetric-algebra universal
  property transports along an isomorphism of the sheaf of modules.** This is the transport
  recorded as missing in the implementation notes of
  `SheafOfModules.nonempty_tensorExteriorSymmetricAlgebras`: the construction produces a symmetric
  algebra of `(moduleSheafification J a).obj F`, and this moves it to any sheaf of modules
  isomorphic to it, which is what makes the construction usable at a sheaf of modules given in
  advance.
* `SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd`: a unital homomorphism of sheaves
  of graded algebras preserves ordered products of degree-one local sections.
* `SheafOfModules.sheafifyUnit_symPow_prod_ι`: **the sheafification unit of the presheaf of
  sectionwise symmetric powers, on a product of degree-one generators, is the ordered product of
  the unit-images of those generators** in the sheafified sectionwise symmetric algebra.
* `SheafOfModules.symPowCmp_eq_sheafifyUnit_comp`: **the comparison morphism factors as the
  sheafification unit followed by a degreewise isomorphism.** This is the identification that
  closes the tag.
* `SheafOfModules.isIso_sheafificationHomEquiv_symm_symPowCmp`: the comparison morphism becomes an
  isomorphism after sheafification.
* `SheafOfModules.symmetricPower_isSheafification`: **Tag 01CG.**

## Implementation notes

**Why a symmetric algebra of `M` has to be transported.** The only symmetric algebra of a sheaf of
modules this development constructs is `SheafOfModules.sectionwiseSymmetricAlgebra J a F`, which is
a symmetric algebra of `(moduleSheafification J a).obj F`. Tag 01CG is about a sheaf of modules `M`
given in advance, and its presheaf of sectionwise symmetric powers is formed from `M.val`, the
sheaf's *own* sections — not from a presheaf whose sheafification is `M`. Taking `a := 𝟙 O♯.obj`
and `F := M.val` makes the two presheaves agree on the nose, at the cost of a symmetric algebra
for `(moduleSheafification J (𝟙 O♯.obj)).obj M.val` rather than for `M`;
`sheafifySectionsIso` is the isomorphism between them and `IsSymmetricAlgebra.comp_iso` is the
transport. No sheafification morphism other than the identity of the ring sheaf would do: the
presheaf `symPow n M.val` is a presheaf of `O♯`-modules, so only `α = 𝟙 O♯.obj` sheafifies it to a
sheaf of `O♯`-modules.

**Universes.** The ring universe and the module universe are *equal* here, which is forced and not
chosen: `SheafOfModules.sectionwiseSymmetricAlgebra` and
`SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra` are stated for
`GradedAlgebra.{w, w}`, so the symmetric algebra this file compares against exists only in the
equal-universe case. `SheafOfModules.GradedAlgebra.symPowCmp` itself, and the two equation families
of `SymmetricPowerSheafification`, hold for modules in `max w a`; it is only the isomorphism
assertion that is pinned. Tag 01CG is stated in the equal-universe case, so nothing the source says
is narrowed.

**Numerals in degrees.** No statement below writes `symPow 1 F` or any other numeral-indexed
sectionwise symmetric power. `SymPow.symmetricPower` sits over the reducible `SymmetricAlgebra`,
a `RingCon` quotient of `TensorAlgebra`, so asking the elaborator to identify `symPow 1 F` with
`Stacks.GradedAlgebra.extendFamily (fun k => symPow k F) 1` sends `whnf` through
`Submodule.mul`/`span` and the quotient and exhausts the heartbeat limit *in the statement*. The
degrees therefore stay variables: `SheafOfModules.GradedAlgebra.mul_congr` supplies the congruence
for a multiplication in two fixed degrees for an *abstract* sheaf of graded algebras, where no
piece can be unfolded, and the degree-one equations are obtained from
`Stacks.GradedAlgebra.sheafifyGen_unit` with no type ascription at all, so the library's own
spelling of the degree-one piece is the one that travels.

**The left-handed ordered product.** Tag 01CG writes the symmetric product of `n` local sections
as `s₀ · (s₁ ⋯ sₙ₋₁)`, which is `Stacks.GradedAlgebra.homogeneousProdLeft`, while the comparison
map of `SymmetricPowerSheafification` is characterized through the right-handed
`Stacks.GradedAlgebra.homogeneousProd`. The two are identified by
`Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd`, and that is what lets the
assembled statement below be the source's.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Sheaf

universe v u w

namespace SheafOfModules.GradedAlgebra

/-! ### Transporting the symmetric-algebra universal property along an isomorphism -/

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {A : GradedAlgebra.{w, w} R} {M N : SheafOfModules.{w} R}

/-- **The symmetric-algebra universal property transports along an isomorphism of the sheaf of
modules.** If `A` is a symmetric algebra of `M` with degree-one generator `gen` and `e : N ≅ M`,
then `A` is a symmetric algebra of `N` with degree-one generator `e.hom ≫ gen`.

This is the transport that the implementation notes of
`SheafOfModules.nonempty_tensorExteriorSymmetricAlgebras` record as not proved there: the
construction of the three algebras of Section 17.21 produces them for the *sheafification* of a
presheaf of modules, and a consumer holding a sheaf of modules in advance gets them only up to the
counit isomorphism. -/
theorem IsSymmetricAlgebra.comp_iso {gen : M ⟶ A.piece 1} (hA : IsSymmetricAlgebra A gen)
    (e : N ≅ M) : IsSymmetricAlgebra A (e.hom ≫ gen) := by
  refine ⟨pairwiseCommutes_comp e.hom hA.1, fun B κ hκ => ?_⟩
  obtain ⟨g, hg, hgu⟩ := hA.2 B (e.inv ≫ κ) (pairwiseCommutes_comp e.inv hκ)
  refine ⟨g, ?_, fun g' hg' => hgu g' ?_⟩
  · simp only [Category.assoc, hg]
    simp
  · simp only [Category.assoc] at hg'
    simp only [← hg', ← Category.assoc, e.inv_hom_id, Category.id_comp]

end Transport

/-! ### Ordered products of degree-one sections and unital homomorphisms -/

section ProdHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}} {A B : GradedAlgebra.{w, w} (toRingCat J Osharp)}

/-- Congruence for the multiplication of a sheaf of graded algebras in two fixed degrees.

This is stated for an *abstract* `A` on purpose. Its two arguments are supplied, at the point of
use, by equations whose sides are spelled in different but definitionally equal ways; with a
concrete `A` whose degree-one piece unfolds to a sectionwise symmetric power, reconciling those
spellings sends the elaborator through the `SymmetricAlgebra` quotient. With `A` abstract no piece
can be unfolded and the reconciliation is immediate. -/
theorem mul_congr (i j : ℤ) (X : Cᵒᵖ) {u u' : (A.piece i).val.obj X}
    {v v' : (A.piece j).val.obj X} (hu : u = u') (hv : v = v') :
    (A.mul i j).app X u v = (A.mul i j).app X u' v' := by rw [hu, hv]

/-- **A unital homomorphism of sheaves of graded algebras preserves ordered products of degree-one
local sections.**

The recursion of `Stacks.GradedAlgebra.homogeneousProd` multiplies on the right, so the degree of
the `(n+1)`-fold product is `(n : ℤ) + 1`, which is exactly the degree the multiplicativity law of
a unital homomorphism produces; no transport appears. -/
theorem UnitalHom.app_homogeneousProd (g : UnitalHom A B) (X : Cᵒᵖ) (n : ℕ)
    (z : Fin n → (A.piece 1).val.obj X) :
    (g.app (n : ℤ)).val.app X (A.toPresheafGradedAlgebra.homogeneousProd X n z) =
      B.toPresheafGradedAlgebra.homogeneousProd X n
        fun i => (g.app 1).val.app X (z i) := by
  induction n with
  | zero => exact g.map_one X
  | succ n ih =>
      show (g.app ((n : ℤ) + 1)).val.app X ((A.mul (n : ℤ) 1).app X _ _) = _
      rw [g.map_mul (n : ℤ) 1 X, ih fun i => z i.castSucc]
      rfl

end ProdHom

end SheafOfModules.GradedAlgebra

namespace SheafOfModules

/-! ### The sheafification unit on products of degree-one generators -/

section UnitProd

open PresheafOfModules CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The sheafification unit of the presheaf of sectionwise symmetric powers, on a product of
degree-one generators.** The unit-image of the product of the generators `s i` is the ordered
product, in the sheafified sectionwise symmetric algebra, of the unit-images of those generators
under the degree-one generator of that algebra.

Since the products of `n` degree-one generators span the `n`-th symmetric power
(`SymPow.ext_of_prod_ι`), this determines the sheafification unit in degree `n`. -/
theorem sheafifyUnit_symPow_prod_ι (n : ℕ) (X : Cᵒᵖ) (s : Fin n → F.obj X) :
    Hom.app (sheafifyUnit (toRingCatMap J a) (symPow n F)) X
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i),
          SymmetricAlgebra.prod_ι_mem _ s⟩ =
      (sectionwiseSymmetricAlgebra J a F).toPresheafGradedAlgebra.homogeneousProd
        X n fun i => (sectionwiseSymmetricAlgebraGen J a F).val.app X
          (Hom.app (sheafifyUnit (toRingCatMap J a) F) X (s i)) := by
  induction n with
  | zero =>
      refine congrArg (fun z => Hom.app (sheafifyUnit (toRingCatMap J a) (symPow 0 F)) X z)
        (symPow_ext F ?_)
      exact Fin.prod_univ_zero
        fun i => SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i)
  | succ n ih =>
      have hcoe : symPowMulApp F n 1 X
            (⟨∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)
              (s i.castSucc), SymmetricAlgebra.prod_ι_mem _ _⟩ : (symPow n F).obj X)
            (Hom.app (symPowGen F) X (s (Fin.last n))) =
          (⟨∏ i : Fin (n + 1), SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i),
            SymmetricAlgebra.prod_ι_mem _ s⟩ : (symPow (n + 1) F).obj X) := by
        refine symPow_ext F ((symPowMulApp_coe F n 1 X _ _).trans ?_)
        rw [symPowGen_coe F X (s (Fin.last n))]
        exact (Fin.prod_univ_castSucc
          fun i => SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i)).symm
      have hlast := (symPowGradedAlgebra F).extend.sheafifyGen_unit (toRingCatMap J a)
        (symPowGen F) X (s (Fin.last n))
      refine Eq.trans (congrArg (fun z =>
        Hom.app (sheafifyUnit (toRingCatMap J a) (symPow (n + 1) F)) X z) hcoe.symm) ?_
      refine Eq.trans ((symPowGradedAlgebra F).extend.sheafify_mul_unit
        (toRingCatMap J a) (n : ℤ) 1 X _ _).symm ?_
      exact GradedAlgebra.mul_congr (n : ℤ) 1 X (ih fun i => s i.castSucc) hlast.symm

end UnitProd

/-! ### The comparison morphism of Tag 01CG becomes an isomorphism -/

section Sheafification

open PresheafOfModules CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The identity of the ring presheaf of a sheaf of commutative rings is locally injective: it is
the identity map on every object. -/
instance isLocallyInjective_toRingCatMap_id :
    Presheaf.IsLocallyInjective J (toRingCatMap J (𝟙 Osharp.obj)) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h => h

/-- The identity of the ring presheaf of a sheaf of commutative rings is locally surjective. -/
instance isLocallySurjective_toRingCatMap_id :
    Presheaf.IsLocallySurjective J (toRingCatMap J (𝟙 Osharp.obj)) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ b => ⟨b, rfl⟩

variable (M : SheafOfModules.{w} (toRingCat J Osharp))

/-- **Sheafifying the sections of a sheaf of modules returns it.** This is the counit of the
sheafification adjunction along the identity of the ring sheaf, which is an isomorphism because
the right adjoint is fully faithful. -/
noncomputable def sheafifySectionsIso :
    (moduleSheafification J (𝟙 Osharp.obj)).obj M.val ≅ M :=
  (asIso ((sheafificationAdjunction (toRingCatMap J (𝟙 Osharp.obj))).counit)).app M

/-- `SheafOfModules.sheafifySectionsIso` undoes the sheafification unit on sections: the triangle
identity of the sheafification adjunction, read on a local section. -/
theorem sheafifySectionsIso_hom_unit (X : Cᵒᵖ) (m : M.val.obj X) :
    (sheafifySectionsIso M).hom.val.app X
        (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) M.val) X m) = m :=
  PresheafOfModules.hom_congr_apply'
    ((sheafificationAdjunction (toRingCatMap J (𝟙 Osharp.obj))).right_triangle_components M) X m

variable (A : GradedAlgebra.{w, w} (toRingCat J Osharp)) (gen : M ⟶ A.piece 1)
  (hgen : GradedAlgebra.PairwiseCommutes gen)
  (hA : GradedAlgebra.IsSymmetricAlgebra A gen)

/-- **The comparison homomorphism of sheaves of graded algebras** from the sheafified sectionwise
symmetric algebra of the sections of `M` to a symmetric algebra `A` of `M`. It is the unique
unital homomorphism carrying one degree-one generator to the other, the generator of `A` being
read on `(moduleSheafification J (𝟙 O♯.obj)).obj M.val` through `sheafifySectionsIso`. -/
noncomputable def symmetricDesc :
    GradedAlgebra.UnitalHom (sectionwiseSymmetricAlgebra J (𝟙 Osharp.obj) M.val) A :=
  (isSymmetricAlgebra_sectionwiseSymmetricAlgebra J (𝟙 Osharp.obj) M.val).isUniversal.desc A
    ((sheafifySectionsIso M).hom ≫ gen) (hA.comp_iso (sheafifySectionsIso M)).1

/-- **The degreewise isomorphism** between the sheafified sectionwise symmetric powers of the
sections of `M` and the homogeneous pieces of a symmetric algebra of `M`: two sheaves of graded
algebras universal for pairwise commutation of the degree-one generator are isomorphic in every
degree. -/
noncomputable def symmetricPieceIso (n : ℤ) :
    (sectionwiseSymmetricAlgebra J (𝟙 Osharp.obj) M.val).piece n ≅ A.piece n :=
  (isSymmetricAlgebra_sectionwiseSymmetricAlgebra J (𝟙 Osharp.obj) M.val).pieceIso
    (hA.comp_iso (sheafifySectionsIso M)) n

/-- The degreewise isomorphism `SheafOfModules.symmetricPieceIso` is, in degree `n`, the
degree-`n` component of the comparison homomorphism `SheafOfModules.symmetricDesc`. -/
theorem symmetricPieceIso_hom (n : ℤ) :
    (symmetricPieceIso M A gen hA n).hom = (symmetricDesc M A gen hA).app n := rfl

/-- The comparison homomorphism carries the degree-one generator of the sheafified sectionwise
symmetric algebra to the degree-one generator of `A`, on the unit-image of a local section. -/
theorem symmetricDesc_gen (X : Cᵒᵖ) (m : M.val.obj X) :
    ((symmetricDesc M A gen hA).app 1).val.app X
        ((sectionwiseSymmetricAlgebraGen J (𝟙 Osharp.obj) M.val).val.app X
          (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) M.val) X m)) =
      gen.val.app X m :=
  (SheafOfModules.hom_congr_app_apply
    ((isSymmetricAlgebra_sectionwiseSymmetricAlgebra J (𝟙 Osharp.obj) M.val).isUniversal
      |>.desc_extends A ((sheafifySectionsIso M).hom ≫ gen)
      (hA.comp_iso (sheafifySectionsIso M)).1) X _).trans
    (congrArg (fun z => gen.val.app X z) (sheafifySectionsIso_hom_unit M X m))

/-- **The comparison morphism of Tag 01CG is the sheafification unit followed by a degreewise
isomorphism.**

Both sides are determined by their values on products of `n` degree-one generators
(`SymPow.ext_of_prod_ι`). There the left-hand side is the ordered product of the images of those
generators under the generator of `A` (`Stacks.GradedAlgebra.cmpSections_prod_ι`), and the
right-hand side is the image under the comparison homomorphism of the ordered product of the
unit-images (`SheafOfModules.sheafifyUnit_symPow_prod_ι`), which is the same ordered product
because a unital homomorphism preserves ordered products
(`SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd`) and carries one generator to the
other (`SheafOfModules.symmetricDesc_gen`). -/
theorem symPowCmp_eq_sheafifyUnit_comp (n : ℕ) :
    A.symPowCmp (hO := (toRingCat J Osharp).property) gen hgen n =
      sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (symPow n M.val) ≫
        (SheafOfModules.forget (toRingCat J Osharp)).map
          (symmetricPieceIso M A gen hA (n : ℤ)).hom := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext ?_
  refine SymPow.ext_of_prod_ι fun s => ?_
  refine Eq.trans (Stacks.GradedAlgebra.cmpSections_prod_ι A.toPresheafGradedAlgebra gen.val
    (fun X x y => hgen X x y) n X s) ?_
  refine Eq.symm (Eq.trans (congrArg
    (fun z => ((symmetricDesc M A gen hA).app (n : ℤ)).val.app X z)
    (sheafifyUnit_symPow_prod_ι (𝟙 Osharp.obj) M.val n X s)) ?_)
  refine Eq.trans (GradedAlgebra.UnitalHom.app_homogeneousProd
    (symmetricDesc M A gen hA) X n _) ?_
  exact congrArg (A.toPresheafGradedAlgebra.homogeneousProd X n)
    (funext fun i => symmetricDesc_gen M A gen hA X (s i))

include hA in
/-- **The comparison morphism of Tag 01CG becomes an isomorphism after sheafification.** This is
the third and last conjunct of `SheafOfModules.symmetricPower_isSheafification` below — the
sheafification clause, which is the whole content of Tag 01CG's symmetric assertion: the presheaf
of sectionwise `n`-th symmetric powers of the sections of `M` has the `n`-th symmetric power of
`M` as its sheafification, with the comparison morphism as the sheafification map. (Tag 01CG
itself states two assertions and no more, the symmetric one and the exterior one; "third" here
counts conjuncts of the formalized statement, not assertions of the source.)

It follows from `SheafOfModules.symPowCmp_eq_sheafifyUnit_comp`: a sheafification unit is locally
bijective, an isomorphism is locally bijective, and a locally bijective morphism into a sheaf of
modules exhibits the latter as the sheafification of its source. -/
@[ega "II 1.7.4" "partial"]
theorem isIso_sheafificationHomEquiv_symm_symPowCmp (n : ℕ) :
    IsIso ((sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).symm
      (A.symPowCmp (hO := (toRingCat J Osharp).property) gen hgen n)) := by
  have hfac : (toPresheaf (toRingCat J Osharp).obj).map
        (A.symPowCmp (hO := (toRingCat J Osharp).property) gen hgen n) =
      (toPresheaf (toRingCat J Osharp).obj).map
          (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (symPow n M.val)) ≫
        (toPresheaf (toRingCat J Osharp).obj).map
          ((SheafOfModules.forget (toRingCat J Osharp)).map
            (symmetricPieceIso M A gen hA (n : ℤ)).hom) :=
    (congrArg (fun h => (toPresheaf (toRingCat J Osharp).obj).map h)
      (symPowCmp_eq_sheafifyUnit_comp M A gen hgen hA n)).trans
      ((toPresheaf (toRingCat J Osharp).obj).map_comp _ _)
  have hinj : Presheaf.IsLocallyInjective J ((toPresheaf (toRingCat J Osharp).obj).map
      ((SheafOfModules.forget (toRingCat J Osharp)).map
        (symmetricPieceIso M A gen hA (n : ℤ)).hom)) := inferInstance
  have hsurj : Presheaf.IsLocallySurjective J ((toPresheaf (toRingCat J Osharp).obj).map
      ((SheafOfModules.forget (toRingCat J Osharp)).map
        (symmetricPieceIso M A gen hA (n : ℤ)).hom)) := inferInstance
  exact Stacks.TensorCoherence.isIso_sheafificationHomEquiv_symm _ _
    (Stacks.TensorCoherence.isLocallyInjective_of_fac J _ hfac.symm inferInstance hinj)
    (Stacks.TensorCoherence.isLocallySurjective_of_fac J _ hfac.symm inferInstance hsurj)

/-- **Every sheaf of modules carries a symmetric algebra**, so the hypotheses of
`SheafOfModules.symmetricPower_isSheafification` are satisfiable and the statement is not
vacuous: take the sheafified sectionwise symmetric algebra of the sections of `M`, with its
degree-one generator read on `M` through `SheafOfModules.sheafifySectionsIso`. -/
@[ega "II 1.7.4" "partial"]
theorem isSymmetricAlgebra_sectionwiseSymmetricAlgebra_val :
    GradedAlgebra.IsSymmetricAlgebra (sectionwiseSymmetricAlgebra J (𝟙 Osharp.obj) M.val)
      ((sheafifySectionsIso M).inv ≫
        sectionwiseSymmetricAlgebraGen J (𝟙 Osharp.obj) M.val) :=
  (isSymmetricAlgebra_sectionwiseSymmetricAlgebra J (𝟙 Osharp.obj) M.val).comp_iso
    (sheafifySectionsIso M).symm

include hgen hA in
/-- **Tag 01CG.** For a sheaf of modules `M` on a site with a sheaf of commutative rings `O♯`, and
a symmetric algebra `A` of `M` in the sense of Section 17.21, the degree-`n` symmetric power
`A.piece n` of `M` is the sheafification of the presheaf `X ↦ Symⁿ_{O♯(X)}(M(X))`.

The presheaf is exhibited together with the sectionwise identification of its sections with
`Symⁿ_{O♯(X)}(M(X))` and the comparison morphism to `A.piece n`; the two equation families fix
the restriction maps and the comparison morphism on products of degree-one generators, and the
last conjunct is the sheafification assertion.

The symmetric algebra is a hypothesis rather than a chosen term: Section 17.21 pins it only up to
canonical isomorphism, and `SheafOfModules.sectionwiseSymmetricAlgebra` together with
`SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra` and
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.comp_iso` shows the hypothesis is satisfiable for
every `M`. -/
@[stacks 01CG "symmetric_power_sheafification"]
theorem symmetricPower_isSheafification (n : ℕ) :
    ∃ P : PresheafOfModules.{w} (toRingCat J Osharp).obj,
      ∃ e : ∀ X : Cᵒᵖ, P.obj X ≃ₗ[(toRingCat J Osharp).obj.obj X]
          SymPow.symmetricPower n ((toRingCat J Osharp).obj.obj X) (M.val.obj X),
        ∃ cmp : P ⟶ (SheafOfModules.forget (toRingCat J Osharp)).obj (A.piece (n : ℤ)),
          (∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (s : Fin n → M.val.obj X)
              (x : SymPow.symmetricPower n ((toRingCat J Osharp).obj.obj X) (M.val.obj X))
              (y : SymPow.symmetricPower n ((toRingCat J Osharp).obj.obj Y) (M.val.obj Y)),
            ((x : SymmetricAlgebra ((toRingCat J Osharp).obj.obj X) (M.val.obj X)) =
                ∏ i : Fin n, SymmetricAlgebra.ι ((toRingCat J Osharp).obj.obj X)
                  (M.val.obj X) (s i)) →
            ((y : SymmetricAlgebra ((toRingCat J Osharp).obj.obj Y) (M.val.obj Y)) =
                ∏ i : Fin n, SymmetricAlgebra.ι ((toRingCat J Osharp).obj.obj Y)
                  (M.val.obj Y) (M.val.map f (s i))) →
            e Y (P.map f ((e X).symm x)) = y) ∧
          (∀ (X : Cᵒᵖ) (s : Fin n → M.val.obj X)
              (x : SymPow.symmetricPower n ((toRingCat J Osharp).obj.obj X) (M.val.obj X)),
            ((x : SymmetricAlgebra ((toRingCat J Osharp).obj.obj X) (M.val.obj X)) =
                ∏ i : Fin n, SymmetricAlgebra.ι ((toRingCat J Osharp).obj.obj X)
                  (M.val.obj X) (s i)) →
            Hom.app cmp X ((e X).symm x) =
              A.toPresheafGradedAlgebra.homogeneousProdLeft X n
                fun i => gen.val.app X (s i)) ∧
          IsIso ((sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).symm cmp) := by
  refine ⟨symPow n M.val, symPowSections n M.val, A.symPowCmp gen hgen n,
    fun X Y f s x y hx hy => ?_, fun X s x hx => ?_,
    isIso_sheafificationHomEquiv_symm_symPowCmp M A gen hgen hA n⟩
  · exact Subtype.ext
      ((symPowSections_map_prod_ι n M.val f s ((symPowSections n M.val X).symm x) hx).trans
        hy.symm)
  · refine Eq.trans (congrArg (fun z => Hom.app (A.symPowCmp gen hgen n) X z)
      (Subtype.ext hx : (symPowSections n M.val X).symm x = ⟨_, SymmetricAlgebra.prod_ι_mem _ s⟩))
      ?_
    exact (Stacks.GradedAlgebra.cmpSections_prod_ι A.toPresheafGradedAlgebra gen.val
      (fun X x y => hgen X x y) n X s).trans
      (A.toPresheafGradedAlgebra.homogeneousProdLeft_eq_homogeneousProd X n _).symm

end Sheafification

end SheafOfModules
