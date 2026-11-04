module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjointAcyclicObjects
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded left derived lower-shriek functor on abelian sheaves

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites and let
`g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi. On abelian sheaves the inverse
image `g⁻¹ : Ab(D) ⥤ Ab(C)` is restriction along `u`; it has a left adjoint `g_! : Ab(C) ⥤
Ab(D)` and a right adjoint `g_*`, so it is exact. Stacks 07AC asserts — in the case of the
constant structure sheaf `ℤ`, which is the case Stacks 07AS invokes — that `g_!` has an
unbounded left derived functor `Lg_! : D(Ab(C)) ⥤ D(Ab(D))` and that `Lg_!` is left adjoint to
`g⁻¹`.

This file is the abelian-sheaf counterpart of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedExistence.lean` and
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedAdjunction.lean`, which do the
same work for sheaves of modules. As there, the criterion of Stacks 0794 is applied with `P`
the class of direct sums of the extensions by zero `j_{U!} ℤ_U` — on abelian sheaves these are
the free abelian sheaves on the representable presheaves — and every hypothesis of that
criterion is discharged here except the one that is the mathematical content of the lemma: that
`g_!` carries a bounded above acyclic complex with terms in `P` to an acyclic complex. That
single statement is carried as a hypothesis.

Nothing is taken over from the module case: the abelian statement is *not* the module statement
for the constant sheaf `ℤ`, because the equivalence `Mod(ℤ^#) ≃ Ab` would have to be
constructed and transported through the whole of the derived machinery. Running the criterion
of Stacks 0794 directly on `Ab(C)` is both shorter and more general — it needs no sheaf of
rings at all.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriek`,
  `Stacks.Cohomology.DerivedLowerShriek.abelianRestriction`: `g_!` and `g⁻¹` on abelian
  sheaves, with their adjunction
  `Stacks.Cohomology.DerivedLowerShriek.abelianAdjunction`.
* `Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb`: `j_{U!} ℤ_U`, the free abelian
  sheaf on the representable presheaf of an object.
* `Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb`: the class `P` of
  direct sums of the `j_{U!} ℤ_U`.
* `Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek` and
  `Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction`: `Lg_!` and `g⁻¹` on the
  unbounded derived categories.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnitsAb`: **Stacks
  03EW (3)** for abelian sheaves — every abelian sheaf is a quotient of a direct sum of free
  abelian sheaves on objects of the site, so `P` generates.
* `Stacks.Cohomology.DerivedLowerShriek.abelianRestriction_exact`: restriction of abelian
  sheaves along a continuous and cocontinuous functor of sites is exact.
* `Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing`: the
  acyclicity statement follows from the object-level vanishing `Ext^{≥1}(j_{U!} ℤ_U, g⁻¹ I) = 0`
  for injective `I`, which is **Stacks 0D6X**. This is what leaves Stacks 07AC for abelian
  sheaves with no open statement about complexes.
* `Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_preservesFiniteLimits`: the
  acyclicity statement holds for free when lower shriek is exact, which by **Stacks 04BH** is the
  case when the source site has fibre products and equalizers preserved by the functor of sites.
* `Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic`:
  **Stacks 07AC** for abelian sheaves, existence, conditional on the acyclicity statement.
* `Stacks.Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic`:
  the resulting left derived functor is absolute, from the same acyclicity statement.
* `Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction`: **Stacks 07AC**
  for abelian sheaves, the derived adjunction `Lg_! ⊣ g⁻¹`, with
  `derivedAbelianLowerShriekAdjunction_unit_fac` and
  `derivedAbelianLowerShriekAdjunction_counit_fac` identifying its unit and counit.
* `Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekAdjunction_unit`: if the
  ordinary unit `F ⟶ g⁻¹ g_! F` is an isomorphism — which for a fully faithful `u` is **Stacks
  077I** — then so is the unit of the derived adjunction, i.e. `g⁻¹ ∘ Lg_! = id`.

## Implementation notes

The two sites have independent universes: `C : Type u₁` with `Category.{v₁} C` and `D : Type
u₂` with `Category.{v₂} D`. The abelian groups live in `AddCommGrpCat.{max v₁ w}` for an
independent `w`, the smallest convention in which the free abelian sheaf on a representable
presheaf of `C` can be formed: `uliftYoneda.{w}.obj U` takes values in `Type (max v₁ w)`. With
`w = v₁` this is the usual `AddCommGrpCat.{v₁}`; the case actually used by Stacks 07AS is a
site in `Type (u + 1)` with morphisms in `Type u` and coefficients in `AddCommGrpCat.{u + 1}`,
i.e. `w = u + 1`.

Whatever Mathlib supplies only for a small site is carried as an instance hypothesis, exactly
as in the module case: sheafification of abelian presheaves in the coefficient universe, the
existence of the left adjoint of restriction (which is `g_!`), the pointwise right Kan
extensions that build `g_*`, and Grothendieck abelianness of the two categories of abelian
sheaves. Each is discharged by search on a site that is essentially small in the coefficient
universe, through `CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`.

`HasExactColimitsOfShape ℕ (Sheaf J AddCommGrpCat.{t})` is not available by search, because
Mathlib's instance for abelian groups is stated at `AB5OfSize.{0, 0}`; it is obtained from
`Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat_addCommGrpCat` and the
sheafification adjunction, which is the same route the module case takes.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

section Colimits

variable {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E)
  [HasSheafify L AddCommGrpCat.{t}]

/-- Coproducts of abelian sheaves indexed by a type as large as the coefficients. This is
`CategoryTheory.Sheaf.instHasColimitsOfShape`, recorded at an index type in the coefficient
universe: instance search does not reach it on its own at that size, because the colimits of
abelian groups it asks for are themselves found only near the end of the search budget. -/
instance hasColimitsOfShape_discrete_sheafAb (ι : Type t) :
    HasColimitsOfShape (Discrete ι) (Sheaf L AddCommGrpCat.{t}) :=
  haveI : HasColimitsOfShape (Discrete ι) AddCommGrpCat.{t} := inferInstance
  CategoryTheory.Sheaf.instHasColimitsOfShape

/-- `ℕ`-indexed colimits of abelian sheaves are exact. They are not available by search: the
Mathlib instance for abelian groups themselves is stated at `AB5OfSize.{0, 0}`, so the one for
`AddCommGrpCat` in an arbitrary universe has to be supplied, after which the sheafification
adjunction transports exactness to sheaves. -/
lemma hasExactColimitsOfShape_nat_sheafAb :
    HasExactColimitsOfShape ℕ (Sheaf L AddCommGrpCat.{t}) :=
  have := hasExactColimitsOfShape_nat_addCommGrpCat.{t}
  (sheafificationAdjunction L AddCommGrpCat.{t}).hasExactColimitsOfShape ℕ

end Colimits

section Generators

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v₁ w}]

/-- `j_{U!} ℤ_U` on abelian sheaves: the free abelian sheaf on the presheaf represented by `U`.
It corepresents sections over `U`, which is what makes it the extension by zero of the constant
sheaf `ℤ` on the localization of the site at `U`. -/
@[sga "4 XVIII 1.4.24", sga "7 VII 1.4" "special case"]
abbrev extensionByZeroUnitAb (U : C) : Sheaf J AddCommGrpCat.{max v₁ w} :=
  (Presheaf.freeAbelianSheaf.{max v₁ w} J).obj (uliftYoneda.{w}.obj U)

/-- **Morphisms out of `j_{U!} ℤ_U` are sections over `U`.** This is the composite of the
free-abelian-sheaf adjunction with the Yoneda lemma. -/
@[sga "4 XVIII 1.4.24" "(a), special case"]
def extensionByZeroUnitAbHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{max v₁ w}) :
    (extensionByZeroUnitAb.{w} J U ⟶ F) ≃ F.obj.obj (op U) :=
  ((Presheaf.freeAbelianSheafAdj.{max v₁ w} J).homEquiv _ _).trans uliftYonedaEquiv.{w}

/-- The identification of morphisms out of `j_{U!} ℤ_U` with sections over `U` is natural in the
target: postcomposing with `g : F ⟶ G` corresponds to applying `g` to sections over `U`. -/
lemma extensionByZeroUnitAbHomEquiv_naturality {U : C}
    {F G : Sheaf J AddCommGrpCat.{max v₁ w}} (f : extensionByZeroUnitAb.{w} J U ⟶ F)
    (g : F ⟶ G) :
    extensionByZeroUnitAbHomEquiv.{w} J U G (f ≫ g) =
      g.hom.app (op U) (extensionByZeroUnitAbHomEquiv.{w} J U F f) := by
  dsimp only [extensionByZeroUnitAbHomEquiv, Equiv.trans_apply]
  rw [(Presheaf.freeAbelianSheafAdj.{max v₁ w} J).homEquiv_naturality_right]
  exact uliftYonedaEquiv_comp.{w} _ _

/-- The class of direct sums of the `j_{U!} ℤ_U`, the class `P` with which Stacks 07AC runs the
criterion of Stacks 0794. -/
def IsSumOfExtensionByZeroUnitsAb :
    ObjectProperty (Sheaf J AddCommGrpCat.{max v₁ w}) := fun F =>
  ∃ (ι : Type (max v₁ w)) (U : ι → C),
    Nonempty ((∐ fun i : ι => extensionByZeroUnitAb.{w} J (U i)) ≅ F)

/-- The class of direct sums of free abelian sheaves on objects contains a zero object: the
direct sum over the empty index family is initial, hence zero. -/
instance containsZero_isSumOfExtensionByZeroUnitsAb :
    (IsSumOfExtensionByZeroUnitsAb.{w} J).ContainsZero := by
  let U₀ : PEmpty.{max v₁ w + 1} → C := fun i => nomatch i
  let E : PEmpty.{max v₁ w + 1} → Sheaf J AddCommGrpCat.{max v₁ w} :=
    fun i => extensionByZeroUnitAb.{w} J (U₀ i)
  have hE : IsInitial (∐ E) :=
    IsInitial.ofUniqueHom (fun _ => Sigma.desc (fun i => isEmptyElim i))
      (fun _ _ => Sigma.hom_ext _ _ (fun i => isEmptyElim i))
  exact ⟨∐ E, hE.isZero, ⟨PEmpty.{max v₁ w + 1}, U₀, ⟨Iso.refl _⟩⟩⟩

/-- The class of direct sums of free abelian sheaves on objects is closed under binary direct
sums: concatenate the two index families. -/
lemma isSumOfExtensionByZeroUnitsAb_biprod
    {F G : Sheaf J AddCommGrpCat.{max v₁ w}}
    (hF : IsSumOfExtensionByZeroUnitsAb.{w} J F)
    (hG : IsSumOfExtensionByZeroUnitsAb.{w} J G) :
    IsSumOfExtensionByZeroUnitsAb.{w} J (F ⊞ G) := by
  obtain ⟨ι, U, ⟨eF⟩⟩ := hF
  obtain ⟨κ, V, ⟨eG⟩⟩ := hG
  refine ⟨ι ⊕ κ, Sum.elim U V, ?_⟩
  let A : ι → Sheaf J AddCommGrpCat.{max v₁ w} :=
    fun i => extensionByZeroUnitAb.{w} J (U i)
  let B : κ → Sheaf J AddCommGrpCat.{max v₁ w} :=
    fun j => extensionByZeroUnitAb.{w} J (V j)
  have hAB : (fun i : ι ⊕ κ => extensionByZeroUnitAb.{w} J (Sum.elim U V i)) =
      Sum.elim A B := by
    funext i
    cases i <;> rfl
  let e : Discrete.functor (fun i : ι ⊕ κ => extensionByZeroUnitAb.{w} J (Sum.elim U V i)) ≅
      Discrete.functor (Sum.elim A B) :=
    Discrete.natIso fun i => eqToIso (congrFun hAB i.as)
  exact ⟨HasColimit.isoOfNatIso e ≪≫
    (coproductIsCoproduct (Sum.elim A B)).coconePointUniqueUpToIso
      (Cofan.combPairIsColimit (coproductIsCoproduct A) (coproductIsCoproduct B)
        (coprodIsCoprod (∐ A) (∐ B))) ≪≫
    (biprod.isoCoprod (∐ A) (∐ B)).symm ≪≫ biprod.mapIso eF eG⟩

/-- **Stacks 03EW (3) for abelian sheaves.** Every abelian sheaf receives an epimorphism from a
direct sum of free abelian sheaves on objects of the site. Index the sum by all pairs `(V, x)`
with `x` a section of `F` over `V`; the component at `(V, x)` is the morphism
`j_{V!} ℤ_V ⟶ F` that `extensionByZeroUnitAbHomEquiv` identifies with `x`. The result is an
epimorphism because a morphism of abelian sheaves is determined by its action on sections over
every object, and every section occurs as one of the indices. -/
theorem exists_epi_isSumOfExtensionByZeroUnitsAb [Small.{max v₁ w} C]
    (F : Sheaf J AddCommGrpCat.{max v₁ w}) :
    ∃ (G : Sheaf J AddCommGrpCat.{max v₁ w})
      (_ : IsSumOfExtensionByZeroUnitsAb.{w} J G) (p : G ⟶ F), Epi p := by
  classical
  let σ : Type max u₁ v₁ w := Σ V : C, (F.obj.obj (op V) : Type (max v₁ w))
  let ι : Type (max v₁ w) := Shrink.{max v₁ w} σ
  let ev : ι ≃ σ := (equivShrink σ).symm
  let U : ι → C := fun i => (ev i).1
  refine ⟨∐ fun i : ι => extensionByZeroUnitAb.{w} J (U i), ⟨ι, U, ⟨Iso.refl _⟩⟩,
    Sigma.desc fun i =>
      (extensionByZeroUnitAbHomEquiv.{w} J (U i) F).symm (ev i).2, ⟨?_⟩⟩
  intro N f g h
  have key (i : ι) :
      f.hom.app (op (ev i).1) (ev i).2 = g.hom.app (op (ev i).1) (ev i).2 := by
    have hh := Sigma.ι (fun i : ι => extensionByZeroUnitAb.{w} J (U i)) i ≫= h
    simp only [Sigma.ι_desc_assoc] at hh
    have he := congrArg (extensionByZeroUnitAbHomEquiv.{w} J (U i) N) hh
    rwa [extensionByZeroUnitAbHomEquiv_naturality, extensionByZeroUnitAbHomEquiv_naturality,
      Equiv.apply_symm_apply] at he
  have hs (s : σ) : f.hom.app (op s.1) s.2 = g.hom.app (op s.1) s.2 := by
    have := key (ev.symm s)
    rwa [ev.apply_symm_apply] at this
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext Y
  ext x
  exact hs ⟨Y.unop, x⟩

end Generators

section Functors

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K] [u.IsCocontinuous J K]
  [HasSheafify J AddCommGrpCat.{max v₁ w}] [HasSheafify K AddCommGrpCat.{max v₁ w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{max v₁ w} J K).IsRightAdjoint]

/-- `g⁻¹ : Ab(D) ⥤ Ab(C)`, restriction of abelian sheaves along the functor of sites. -/
abbrev abelianRestriction :
    Sheaf K AddCommGrpCat.{max v₁ w} ⥤ Sheaf J AddCommGrpCat.{max v₁ w} :=
  u.sheafPushforwardContinuous AddCommGrpCat.{max v₁ w} J K

/-- `g_! : Ab(C) ⥤ Ab(D)`, the lower-shriek functor on abelian sheaves: the left adjoint of
restriction. -/
abbrev abelianLowerShriek :
    Sheaf J AddCommGrpCat.{max v₁ w} ⥤ Sheaf K AddCommGrpCat.{max v₁ w} :=
  u.sheafPullback AddCommGrpCat.{max v₁ w} J K

/-- The ordinary adjunction `g_! ⊣ g⁻¹` on abelian sheaves. -/
abbrev abelianAdjunction :
    abelianLowerShriek.{w} J K u ⊣ abelianRestriction.{w} J K u :=
  u.sheafAdjunctionContinuous AddCommGrpCat.{max v₁ w} J K

/-- The lower-shriek functor on abelian sheaves is a left adjoint. -/
instance isLeftAdjoint_abelianLowerShriek :
    (abelianLowerShriek.{w} J K u).IsLeftAdjoint :=
  (abelianAdjunction.{w} J K u).isLeftAdjoint

/-- The lower-shriek functor on abelian sheaves preserves colimits. -/
instance preservesColimits_abelianLowerShriek :
    PreservesColimitsOfSize.{max v₁ w, max v₁ w} (abelianLowerShriek.{w} J K u) :=
  (abelianAdjunction.{w} J K u).leftAdjoint_preservesColimits

/-- The lower-shriek functor on abelian sheaves preserves zero morphisms. -/
instance preservesZeroMorphisms_abelianLowerShriek :
    (abelianLowerShriek.{w} J K u).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- The lower-shriek functor on abelian sheaves is additive, being a left adjoint between
additive categories. -/
instance additive_abelianLowerShriek : (abelianLowerShriek.{w} J K u).Additive :=
  haveI : PreservesColimitsOfShape (Discrete WalkingPair)
      (abelianLowerShriek.{w} J K u) :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift.{max v₁ w, 0})) _
  haveI : PreservesBinaryBiproducts (abelianLowerShriek.{w} J K u) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The lower-shriek functor on abelian sheaves preserves finite colimits. -/
instance preservesFiniteColimits_abelianLowerShriek :
    PreservesFiniteColimits (abelianLowerShriek.{w} J K u) :=
  haveI : PreservesColimitsOfSize.{0, 0} (abelianLowerShriek.{w} J K u) :=
    preservesColimitsOfSize_shrink _
  inferInstance

/-- The lower-shriek functor on abelian sheaves preserves `ℕ`-indexed colimits. -/
instance preservesColimitsOfShape_nat_abelianLowerShriek :
    PreservesColimitsOfShape ℕ (abelianLowerShriek.{w} J K u) :=
  haveI : PreservesColimitsOfSize.{0, 0} (abelianLowerShriek.{w} J K u) :=
    preservesColimitsOfSize_shrink _
  inferInstance

section Restriction

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max v₁ w}, u.op.HasPointwiseRightKanExtension F]

/-- `g_* : Ab(C) ⥤ Ab(D)`, the direct image of abelian sheaves along the cocontinuous functor
of sites, the right adjoint of restriction. -/
abbrev abelianPushforward :
    Sheaf J AddCommGrpCat.{max v₁ w} ⥤ Sheaf K AddCommGrpCat.{max v₁ w} :=
  u.sheafPushforwardCocontinuous AddCommGrpCat.{max v₁ w} J K

/-- The adjunction `g⁻¹ ⊣ g_*` of the morphism of topoi, on abelian sheaves. -/
abbrev abelianPushforwardAdjunction :
    abelianRestriction.{w} J K u ⊣ abelianPushforward.{w} J K u :=
  u.sheafAdjunctionCocontinuous AddCommGrpCat.{max v₁ w} J K

/-- Restriction of abelian sheaves preserves colimits. -/
instance preservesColimits_abelianRestriction :
    PreservesColimitsOfSize.{max v₁ w, max v₁ w} (abelianRestriction.{w} J K u) :=
  (abelianPushforwardAdjunction.{w} J K u).leftAdjoint_preservesColimits

/-- Restriction of abelian sheaves preserves finite colimits. -/
instance preservesFiniteColimits_abelianRestriction :
    PreservesFiniteColimits (abelianRestriction.{w} J K u) :=
  haveI : PreservesColimitsOfSize.{0, 0} (abelianRestriction.{w} J K u) :=
    preservesColimitsOfSize_shrink _
  inferInstance

omit [HasSheafify J AddCommGrpCat.{max v₁ w}] [HasSheafify K AddCommGrpCat.{max v₁ w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{max v₁ w} J K).IsRightAdjoint] in
/-- **Restriction of abelian sheaves along a continuous and cocontinuous functor of sites is
exact.** Left exactness holds because restriction is the right adjoint of the lower-shriek
functor; right exactness is cocontinuity of the functor of sites, through which restriction
acquires the right adjoint `g_*` of the morphism of topoi. -/
theorem abelianRestriction_exact :
    exactFunctor (Sheaf K AddCommGrpCat.{max v₁ w}) (Sheaf J AddCommGrpCat.{max v₁ w})
      (abelianRestriction.{w} J K u) :=
  ⟨inferInstanceAs (PreservesFiniteLimits (abelianRestriction.{w} J K u)),
    preservesFiniteColimits_abelianRestriction.{w} J K u⟩

/-- Restriction of abelian sheaves is additive, being exact. -/
instance additive_abelianRestriction : (abelianRestriction.{w} J K u).Additive :=
  exactFunctor_le_additiveFunctor _ _ _ (abelianRestriction_exact.{w} J K u)

end Restriction

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The acyclicity statement to which Stacks 07AC reduces the existence of `Lg_!` on abelian
sheaves: the lower-shriek functor carries a bounded above acyclic complex whose terms are direct
sums of the `j_{U!} ℤ_U` to an acyclic complex. -/
abbrev AbelianLowerShriekAcyclic : Prop :=
  ∀ (a : ℤ) (L : CochainComplex (Sheaf J AddCommGrpCat.{max v₁ w}) ℤ), L.IsStrictlyLE a →
    (∀ n, IsSumOfExtensionByZeroUnitsAb.{w} J (L.X n)) → L.Acyclic →
    (((abelianLowerShriek.{w} J K u).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic

/-- Lower shriek on abelian sheaves, applied degreewise to unbounded homotopy categories. -/
abbrev abelianLowerShriekOnHomotopy :
    HomotopyCategory (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Sheaf K AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ) :=
  (abelianLowerShriek.{w} J K u).mapHomotopyCategory (ComplexShape.up ℤ)

omit [u.IsCocontinuous J K] [HasSheafify K AddCommGrpCat.{max v₁ w}] in
/-- **The acyclicity statement is automatic when lower shriek is exact.** An exact functor
preserves the homology of a complex, so it carries an acyclic complex to an acyclic complex,
whatever its terms. Lower shriek on abelian sheaves is always right exact, being a left adjoint;
it is left exact as soon as the source site has fibre products and equalizers which `u`
preserves, which is **Stacks 04BH**
(`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`). So on a site where that holds —
for instance a slice of one of the big sites of schemes — Stacks 07AC for abelian sheaves is
unconditional. -/
theorem abelianLowerShriekAcyclic_of_preservesFiniteLimits
    [PreservesFiniteLimits (abelianLowerShriek.{w} J K u)] :
    AbelianLowerShriekAcyclic.{w} J K u := by
  intro a L _ _ hL i
  rw [HomologicalComplex.exactAt_iff]
  have h := hL i
  rw [HomologicalComplex.exactAt_iff] at h
  exact h.map (abelianLowerShriek.{w} J K u)

omit [u.IsCocontinuous J K] in
/-- **The acyclicity statement of Stacks 07AC follows from the vanishing of Stacks 0D6X.** If
`Ext^n(j_{U!} ℤ_U, g⁻¹ I) = 0` for every object `U` of the source site, every injective abelian
sheaf `I` on the target site and every `n ≥ 1`, then the lower-shriek functor carries every
bounded above acyclic complex with terms in `P` to an acyclic complex.

That vanishing is **Stacks 0D6X**: `Ext^n(j_{U!} ℤ_U, F)` is the degree-`n` cohomology of `F`
over `U`, and the cohomology of the restriction of an injective abelian sheaf vanishes in
positive degrees, by the Čech computation of the source. So this reduces the whole of Stacks
07AC for abelian sheaves to an object-level cohomology vanishing, with no statement about
complexes left open.

The reduction is `CategoryTheory.Adjunction.map_acyclic_of_extAcyclic` for the adjunction
`g_! ⊣ g⁻¹`: the hypothesis says exactly that each `j_{U!} ℤ_U` is `Ext`-acyclic for it, the
class of `Ext`-acyclic objects is closed under the direct sums that make up the terms of such a
complex, and `Ext`-acyclicity transports along the isomorphism exhibiting a term as such a
sum. -/
theorem abelianLowerShriekAcyclic_of_ext_vanishing
    [HasExt.{t} (Sheaf J AddCommGrpCat.{max v₁ w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max v₁ w})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{max v₁ w})]
    (hExt : ∀ (U : C) (I : Sheaf K AddCommGrpCat.{max v₁ w}), Injective I → ∀ n : ℕ, 1 ≤ n →
      Subsingleton (Abelian.Ext (extensionByZeroUnitAb.{w} J U)
        ((abelianRestriction.{w} J K u).obj I) n)) :
    AbelianLowerShriekAcyclic.{w} J K u := by
  intro a L hLE hLP hLac
  have := hLE
  refine (abelianAdjunction.{w} J K u).map_acyclic_of_extAcyclic L a hLac fun n => ?_
  obtain ⟨ι, U, ⟨e⟩⟩ := hLP n
  exact (abelianAdjunction.{w} J K u).extAcyclic_of_iso e
    ((abelianAdjunction.{w} J K u).extAcyclic_coproduct _ fun i => hExt (U i))

omit [u.IsCocontinuous J K] in
/-- **Stacks 07AC for abelian sheaves**, existence, conditional on its one remaining input. If
the lower-shriek functor carries every bounded above acyclic complex whose terms are direct sums
of the free abelian sheaves on objects of the site to an acyclic complex, then it has an
unbounded left derived functor. Every other hypothesis of the criterion of Stacks 0794 holds
here, with the class of objects taken to be the direct sums of the `j_{U!} ℤ_U`: that class
contains a zero object, is closed under binary direct sums and generates, `ℕ`-indexed colimits
exist and are exact in abelian sheaves on either site, and the lower-shriek functor is additive
and commutes with all colimits, being a left adjoint. -/
theorem hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic [Small.{max v₁ w} C]
    (hFP : AbelianLowerShriekAcyclic.{w} J K u) :
    (abelianLowerShriekOnHomotopy.{w} J K u ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ)) := by
  have := hasExactColimitsOfShape_nat_sheafAb.{max v₁ w} J
  have := hasExactColimitsOfShape_nat_sheafAb.{max v₁ w} K
  exact CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    (abelianLowerShriek.{w} J K u) (IsSumOfExtensionByZeroUnitsAb.{w} J)
    (fun _ _ => isSumOfExtensionByZeroUnitsAb_biprod.{w} J)
    (fun F => exists_epi_isSumOfExtensionByZeroUnitsAb.{w} J F) hFP

omit [u.IsCocontinuous J K] in
/-- **The left derived lower-shriek functor on abelian sheaves is absolute.** Under the same
acyclicity statement, `Lg_!` stays a left derived functor after composition with any functor out
of `D(Ab(D))`, because it is constructed by resolutions. Taking that functor to be derived
restriction is the second hypothesis of the derived adjunction of Stacks 09T5. -/
theorem isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic [Small.{max v₁ w} C]
    (hFP : AbelianLowerShriekAcyclic.{w} J K u)
    {H : Type*} [Category H]
    (LF : HomotopyCategory (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ) ⥤ H)
    [LF.IsLocalization (HomotopyCategory.quasiIso
      (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))]
    (Lg : H ⥤ DerivedCategory (Sheaf K AddCommGrpCat.{max v₁ w}))
    (α : LF ⋙ Lg ⟶ abelianLowerShriekOnHomotopy.{w} J K u ⋙ DerivedCategory.Qh)
    [Lg.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
      (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))]
    {H' : Type*} [Category H']
    (G : DerivedCategory (Sheaf K AddCommGrpCat.{max v₁ w}) ⥤ H') :
    (Lg ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator LF Lg G).inv ≫ Functor.whiskerRight α G)
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ)) := by
  have := hasExactColimitsOfShape_nat_sheafAb.{max v₁ w} J
  have := hasExactColimitsOfShape_nat_sheafAb.{max v₁ w} K
  exact CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex
    (abelianLowerShriek.{w} J K u) (IsSumOfExtensionByZeroUnitsAb.{w} J)
    (fun _ _ => isSumOfExtensionByZeroUnitsAb_biprod.{w} J)
    (fun F => exists_epi_isSumOfExtensionByZeroUnitsAb.{w} J F) hFP LF Lg α G

section Adjunction

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max v₁ w}, u.op.HasPointwiseRightKanExtension F]

/-- Restriction of abelian sheaves applied degreewise to unbounded homotopy categories. -/
abbrev abelianRestrictionOnHomotopy :
    HomotopyCategory (Sheaf K AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ) :=
  (abelianRestriction.{w} J K u).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The ordinary adjunction `g_! ⊣ g⁻¹` of abelian sheaves, read on the unbounded homotopy
categories. Its unit and counit are the degreewise ones. -/
abbrev abelianHomotopyAdjunction :
    abelianLowerShriekOnHomotopy.{w} J K u ⊣ abelianRestrictionOnHomotopy.{w} J K u :=
  (abelianAdjunction.{w} J K u).mapHomotopyCategory (ComplexShape.up ℤ)

/-- Restriction of abelian sheaves, induced on the unbounded derived categories by
exactness. -/
abbrev derivedAbelianRestriction :
    DerivedCategory (Sheaf K AddCommGrpCat.{max v₁ w}) ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{max v₁ w}) :=
  (abelianRestriction.{w} J K u).mapDerivedCategory

/-- The comparison from degreewise restriction to restriction on the derived categories. It is
an isomorphism, restriction being exact. -/
abbrev derivedAbelianRestrictionComparison :
    abelianRestrictionOnHomotopy.{w} J K u ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedAbelianRestriction.{w} J K u :=
  (abelianRestriction.{w} J K u).mapDerivedCategoryFactorsh.inv

/-- Restriction on the derived categories is the right derived functor of degreewise
restriction, its comparison transformation being invertible. -/
instance isRightDerivedFunctor_derivedAbelianRestriction :
    (derivedAbelianRestriction.{w} J K u).IsRightDerivedFunctor
      (derivedAbelianRestrictionComparison.{w} J K u)
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    ((abelianRestriction.{w} J K u).mapDerivedCategoryFactorsh)

variable [(abelianLowerShriekOnHomotopy.{w} J K u ⋙
  DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))]

/-- The canonical unbounded left derived lower-shriek functor `Lg_!` on abelian sheaves. -/
abbrev derivedAbelianLowerShriek :
    DerivedCategory (Sheaf J AddCommGrpCat.{max v₁ w}) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{max v₁ w}) :=
  (abelianLowerShriekOnHomotopy.{w} J K u ⋙ DerivedCategory.Qh).totalLeftDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))

/-- The comparison from derived lower shriek to degreewise lower shriek on the homotopy
category, i.e. the counit exhibiting `Lg_!` as a left derived functor. -/
abbrev derivedAbelianLowerShriekComparison :
    DerivedCategory.Qh ⋙ derivedAbelianLowerShriek.{w} J K u ⟶
      abelianLowerShriekOnHomotopy.{w} J K u ⋙ DerivedCategory.Qh :=
  (abelianLowerShriekOnHomotopy.{w} J K u ⋙ DerivedCategory.Qh).totalLeftDerivedCounit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))

variable [IsGrothendieckAbelian.{max v₁ w} (Sheaf K AddCommGrpCat.{max v₁ w})]
  [(derivedAbelianLowerShriek.{w} J K u ⋙
    derivedAbelianRestriction.{w} J K u).IsLeftDerivedFunctor
    ((Functor.associator DerivedCategory.Qh (derivedAbelianLowerShriek.{w} J K u)
      (derivedAbelianRestriction.{w} J K u)).inv ≫
      Functor.whiskerRight (derivedAbelianLowerShriekComparison.{w} J K u)
        (derivedAbelianRestriction.{w} J K u))
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))]

/-- **Stacks 07AC for abelian sheaves**, the derived adjunction: the unbounded left derived
lower-shriek functor on abelian sheaves is left adjoint to derived restriction. This is Stacks
09T5 on the unbounded derived category of the Grothendieck abelian category `Ab(D)`. -/
def derivedAbelianLowerShriekAdjunction :
    derivedAbelianLowerShriek.{w} J K u ⊣ derivedAbelianRestriction.{w} J K u :=
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction
    (abelianHomotopyAdjunction.{w} J K u)
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))
    (derivedAbelianLowerShriekComparison.{w} J K u)
    (derivedAbelianRestrictionComparison.{w} J K u)

/-- **Stacks 07AC for abelian sheaves**, unit factorization: the unit of the derived adjunction
is the one induced by the unit of the ordinary lower-shriek--restriction adjunction, through the
two canonical comparison transformations. -/
theorem derivedAbelianLowerShriekAdjunction_unit_fac
    (M : HomotopyCategory (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ)) :
    (derivedAbelianLowerShriekAdjunction.{w} J K u).unit.app (DerivedCategory.Qh.obj M) ≫
        (derivedAbelianRestriction.{w} J K u).map
          ((derivedAbelianLowerShriekComparison.{w} J K u).app M) =
      DerivedCategory.Qh.map ((abelianHomotopyAdjunction.{w} J K u).unit.app M) ≫
        (derivedAbelianRestrictionComparison.{w} J K u).app
          ((abelianLowerShriekOnHomotopy.{w} J K u).obj M) :=
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction_unit_app
    (abelianHomotopyAdjunction.{w} J K u)
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))
    (derivedAbelianLowerShriekComparison.{w} J K u)
    (derivedAbelianRestrictionComparison.{w} J K u) M

/-- **Stacks 07AC for abelian sheaves**, counit factorization: the counit of the derived
adjunction is the one induced by the counit of the ordinary lower-shriek--restriction
adjunction, through the two canonical comparison transformations. -/
theorem derivedAbelianLowerShriekAdjunction_counit_fac
    (N : HomotopyCategory (Sheaf K AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ)) :
    (derivedAbelianLowerShriek.{w} J K u).map
          ((derivedAbelianRestrictionComparison.{w} J K u).app N) ≫
        (derivedAbelianLowerShriekAdjunction.{w} J K u).counit.app
          (DerivedCategory.Qh.obj N) =
      (derivedAbelianLowerShriekComparison.{w} J K u).app
          ((abelianRestrictionOnHomotopy.{w} J K u).obj N) ≫
        DerivedCategory.Qh.map ((abelianHomotopyAdjunction.{w} J K u).counit.app N) :=
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction_counit_app
    (abelianHomotopyAdjunction.{w} J K u)
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))
    (derivedAbelianLowerShriekComparison.{w} J K u)
    (derivedAbelianRestrictionComparison.{w} J K u) N

/-- **The unit of the derived adjunction is an isomorphism as soon as the ordinary one is.**
For a fully faithful `u` the ordinary unit `F ⟶ g⁻¹ g_! F` is an isomorphism — that is Stacks
077I — and then `g⁻¹ ∘ Lg_! = id` on the unbounded derived category, which is the last assertion
of Stacks 07AS.

The argument is uniqueness of left derived functors. Degreewise, an invertible unit stays
invertible on complexes and hence on the homotopy category, and derived restriction is
degreewise restriction up to the invertible comparison; so the transformation that exhibits the
identity of `D(Ab(C))` as a candidate left derived functor of `Qh ⋙ Lg_! ⋙ g⁻¹` is invertible,
which makes the identity a left derived functor of it. The unit of the derived adjunction is by
construction the canonical comparison between that candidate and the actual left derived functor
`Lg_! ⋙ g⁻¹`, and a comparison between two left derived functors of the same functor is
invertible. -/
theorem isIso_derivedAbelianLowerShriekAdjunction_unit
    (hunit : IsIso (abelianAdjunction.{w} J K u).unit) :
    IsIso (derivedAbelianLowerShriekAdjunction.{w} J K u).unit := by
  have := hunit
  set A := Sheaf J AddCommGrpCat.{max v₁ w} with hA
  set W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ) with hW
  set Gh := abelianLowerShriekOnHomotopy.{w} J K u with hGh
  set Lg := derivedAbelianLowerShriek.{w} J K u with hLg
  set Fd := derivedAbelianRestriction.{w} J K u with hFd
  set α := derivedAbelianLowerShriekComparison.{w} J K u with hα
  set β := derivedAbelianRestrictionComparison.{w} J K u with hβ
  set adjh := abelianHomotopyAdjunction.{w} J K u with hadjh
  have hadjhunit : ∀ X, IsIso (adjh.unit.app X) := by
    rintro ⟨X⟩
    let v := (NatTrans.mapHomologicalComplex (abelianAdjunction.{w} J K u).unit
      (ComplexShape.up ℤ)).app X
    have : ∀ n, IsIso (v.f n) := by
      intro n
      show IsIso ((abelianAdjunction.{w} J K u).unit.app (X.X n))
      infer_instance
    have : IsIso v := HomologicalComplex.Hom.isIso_of_components _
    show IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map v)
    infer_instance
  have : IsIso adjh.unit := NatIso.isIso_of_isIso_app _
  have : IsIso β := by
    rw [hβ]
    infer_instance
  set ηcmp := DerivedCategory.Qh.rightUnitor.hom ≫ DerivedCategory.Qh.leftUnitor.inv ≫
    Functor.whiskerRight adjh.unit DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Gh β ≫
    (Functor.associator _ _ _).inv with hηcmp
  have hiso : IsIso ηcmp := by
    rw [hηcmp]
    infer_instance
  have hid : (𝟭 (DerivedCategory A)).IsLeftDerivedFunctor ηcmp W :=
    Functor.isLeftDerivedFunctor_of_inverts W (𝟭 (DerivedCategory A)) (asIso ηcmp)
  exact (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift (Lg ⋙ Fd)
    ((Functor.associator DerivedCategory.Qh Lg Fd).inv ≫ Functor.whiskerRight α Fd) W
    (𝟭 (DerivedCategory A)) ηcmp).mp hid

/-- **The last assertion of Stacks 07AS for abelian sheaves**: restriction after derived lower
shriek is canonically the identity of `D(Ab(C))`, whenever the ordinary unit is an isomorphism
(Stacks 077I). -/
def derivedAbelianLowerShriekRestrictionIso
    (hunit : IsIso (abelianAdjunction.{w} J K u).unit) :
    derivedAbelianLowerShriek.{w} J K u ⋙ derivedAbelianRestriction.{w} J K u ≅
      𝟭 (DerivedCategory (Sheaf J AddCommGrpCat.{max v₁ w})) :=
  have := isIso_derivedAbelianLowerShriekAdjunction_unit.{w} J K u hunit
  (asIso (derivedAbelianLowerShriekAdjunction.{w} J K u).unit).symm

end Adjunction

end Derived

end Functors

end Stacks.Cohomology.DerivedLowerShriek

end
