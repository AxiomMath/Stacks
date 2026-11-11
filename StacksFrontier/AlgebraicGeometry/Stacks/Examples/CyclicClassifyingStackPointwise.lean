module

public import StacksFrontier.AlgebraicGeometry.Stacks.Examples.CyclicClassifyingStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackOfGroupoidModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ShiftedSumOfModulesAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage

/-!
# The pointwise quotient `[S/_p(ℤ/pℤ)]` as a dense subsite of `[S/(ℤ/pℤ)]`

Let `k` be a field, `S = Spec k[x]` and `G = ℤ/pℤ`. The classifying stack `𝒳 = [S/G]` of
`Stacks.Examples.UnboundedDerivedPushforward.cyclicClassifyingStack` is the hom-shrunk model of
the quotient stack of the trivial action groupoid of `G_S` on `S`. Its pointwise groupoid
fibration `𝒫 = [S/_pG]` (the presentation of Stacks 044Q, before stackification) maps fully
faithfully to `𝒳`, and this map is a dense subsite inclusion for the two fppf topologies
(Stacks 044X, via `AlgebraicGeometry.Stack.isDenseSubsite_pointwiseToQuotientStack`). So
restriction of sheaves of modules from `𝒳` to `𝒫` is an equivalence. This file sets up that
restriction, the object `U` of `𝒫` given by the trivial torsor over `S`, and the ring map from
`Γ(S, 𝒪_S)` to the global sections of the structure sheaf of `𝒫`. It is the stage on which the
cohomology of `𝒪_𝒳` is computed by Čech cochains for the cover `U` of the final object.

## Main definitions

* `Stacks.Examples.UnboundedDerivedPushforward.cyclicPointwise`: the pointwise groupoid
  fibration `𝒫`.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicPointwiseInclusion`: the functor
  `𝒫 ⥤ 𝒳`.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicPointwiseRestriction`: restriction of
  modules `Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒫)`, an equivalence.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicPointwiseUnitObject`: the object `U` of `𝒫`
  over the final object `S` of the site.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicPointwiseBaseRingHom`: the ring map
  `Γ(S, 𝒪_S) ⟶ Γ(𝒫, 𝒪_𝒫)`.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules

universe u

namespace Stacks.Examples.UnboundedDerivedPushforward

variable (p : ℕ) [NeZero p] {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- The trivial action groupoid of `(ℤ/pℤ)_S` on `S`, whose quotient stack is `[S/(ℤ/pℤ)]`. -/
abbrev cyclicActionGroupoid :=
  Stack.trivialActionGroupoid (cyclicGroupSpace p 𝒞 hS)

/-- **The pointwise quotient `[S/_p(ℤ/pℤ)]`**: the category fibred in groupoids attached to the
presheaf of groupoids `T ↦ (S(T), G(T) ×_{S(T)} S(T))` of the trivial action groupoid. -/
abbrev cyclicPointwise : BasedCategory (BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS) :=
  presheafOfGroupoids
    (Stack.evaluationGroupoidFunctor (cyclicActionGroupoid p 𝒞 hS).toGroupoidInFunctors)

/-- The pointwise quotient is fibred in groupoids. -/
theorem isFiberedInGroupoids_cyclicPointwise :
    (cyclicPointwise p 𝒞 hS).p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_presheafOfGroupoids _

/-- The category over the site underlying `[S/(ℤ/pℤ)]`: the hom-shrunk model of the quotient
stack of the trivial action groupoid. It is the underlying based category of
`Stacks.Examples.UnboundedDerivedPushforward.cyclicClassifyingStack`, by definition. -/
abbrev cyclicStackModel : BasedCategory (BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS) :=
  Stack.quotientStackSmall (cyclicActionGroupoid p 𝒞 hS)

/-- The underlying based category of `[S/(ℤ/pℤ)]` is `cyclicStackModel`. -/
theorem cyclicClassifyingStack_val_val.{w} :
    (cyclicClassifyingStack.{u, w} p 𝒞 hS).val.val = cyclicStackModel p 𝒞 hS :=
  rfl

/-- `[S/(ℤ/pℤ)]` is fibred in groupoids. -/
theorem isFiberedInGroupoids_cyclicStackModel :
    (cyclicStackModel p 𝒞 hS).p.IsFiberedInGroupoids :=
  Stack.isFiberedInGroupoids_quotientStackSmall _

/-- **The inclusion `[S/_p(ℤ/pℤ)] ⥤ [S/(ℤ/pℤ)]`**: the canonical map to the quotient stack,
followed by the hom-shrinking equivalence. -/
def cyclicPointwiseInclusion : (cyclicPointwise p 𝒞 hS).obj ⥤ (cyclicStackModel p 𝒞 hS).obj :=
  letI := Stack.locallySmall_quotientStack (cyclicActionGroupoid p 𝒞 hS)
  Stack.pointwiseToQuotientStack _ ⋙ ShrinkHoms.functor _

/-- The inclusion of the pointwise quotient is fully faithful. -/
def cyclicPointwiseInclusionFullyFaithful :
    (cyclicPointwiseInclusion p 𝒞 hS).FullyFaithful :=
  letI := Stack.locallySmall_quotientStack (cyclicActionGroupoid p 𝒞 hS)
  (Stack.fullyFaithfulPointwiseToQuotientStack _).comp
    (ShrinkHoms.equivalence _).fullyFaithfulFunctor

/-- The inclusion of the pointwise quotient is full. -/
instance : (cyclicPointwiseInclusion p 𝒞 hS).Full :=
  (cyclicPointwiseInclusionFullyFaithful p 𝒞 hS).full

/-- The inclusion of the pointwise quotient is faithful. -/
instance : (cyclicPointwiseInclusion p 𝒞 hS).Faithful :=
  (cyclicPointwiseInclusionFullyFaithful p 𝒞 hS).faithful

/-- The inclusion of the pointwise quotient lies over the site. -/
theorem cyclicPointwiseInclusion_comp_p :
    cyclicPointwiseInclusion p 𝒞 hS ⋙ (cyclicStackModel p 𝒞 hS).p = (cyclicPointwise p 𝒞 hS).p := by
  have := Stack.locallySmall_quotientStack (cyclicActionGroupoid p 𝒞 hS)
  have h : ShrinkHoms.functor (Stack.quotientStack (cyclicActionGroupoid p 𝒞 hS)).obj ⋙
      ShrinkHoms.inverse _ = 𝟭 _ :=
    CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
      change (equivShrink _).symm (equivShrink _ f) = 𝟙 _ ≫ f ≫ 𝟙 _
      simp)
  change Stack.pointwiseToQuotientStack _ ⋙ (ShrinkHoms.functor _ ⋙ ShrinkHoms.inverse _) ⋙
    (Stack.quotientStack _).p = _
  rw [h, Functor.id_comp]
  exact (Stack.isFibredOneMorphism_pointwiseToQuotientStack _).comp_eq

/-- The inclusion of the pointwise quotient lies over the site, on morphisms. -/
theorem cyclicStackModel_p_map_cyclicPointwiseInclusion_map
    {x y : (cyclicPointwise p 𝒞 hS).obj} (f : x ⟶ y) :
    (cyclicStackModel p 𝒞 hS).p.map ((cyclicPointwiseInclusion p 𝒞 hS).map f) =
      (cyclicPointwise p 𝒞 hS).p.map f := by
  have key : ∀ {a b : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS} (h₁ : a = a) (h₂ : b = b)
      (g : a ⟶ b), eqToHom h₁ ≫ g ≫ eqToHom h₂ = g := by
    intros
    simp
  exact (Functor.congr_hom (cyclicPointwiseInclusion_comp_p p 𝒞 hS) f).trans (key _ _ _)

/-- `[S/(ℤ/pℤ)]` is essentially small at the universe of the schemes. -/
instance essentiallySmall_cyclicStackModel : EssentiallySmall.{u} (cyclicStackModel p 𝒞 hS).obj :=
  Stack.essentiallySmall_obj_algebraicStack 𝒞 _ hS (cyclicClassifyingStack.{u, u} p 𝒞 hS)

/-- The pointwise quotient is essentially small at the universe of the schemes: it embeds fully
faithfully into `[S/(ℤ/pℤ)]`. -/
instance essentiallySmall_cyclicPointwise : EssentiallySmall.{u} (cyclicPointwise p 𝒞 hS).obj :=
  essentiallySmall_of_fully_faithful (cyclicPointwiseInclusion p 𝒞 hS)

/-- The fppf topology on the pointwise quotient. -/
abbrev cyclicPointwiseTopology : GrothendieckTopology (cyclicPointwise p 𝒞 hS).obj :=
  BigFppfOver.associatedTopology 𝒞 _ hS (cyclicPointwise p 𝒞 hS).p .fppf

/-- The fppf topology on `[S/(ℤ/pℤ)]`. -/
abbrev cyclicStackTopology : GrothendieckTopology (cyclicStackModel p 𝒞 hS).obj :=
  BigFppfOver.associatedTopology 𝒞 _ hS (cyclicStackModel p 𝒞 hS).p .fppf

/-- **The pointwise quotient is cover-dense in `[S/(ℤ/pℤ)]`**: so it is in the quotient stack
(`AlgebraicGeometry.Stack.isCoverDense_pointwiseToQuotientStack`), and the hom-shrinking
equivalence does not change the images of the sieves in the site. -/
theorem isCoverDense_cyclicPointwiseInclusion :
    (cyclicPointwiseInclusion p 𝒞 hS).IsCoverDense (cyclicStackTopology p 𝒞 hS) := by
  have := Stack.locallySmall_quotientStack (cyclicActionGroupoid p 𝒞 hS)
  have hQ := Stack.isCoverDense_pointwiseToQuotientStack (cyclicActionGroupoid p 𝒞 hS)
  constructor
  intro y
  have hy := hQ.is_cover (ShrinkHoms.fromShrinkHoms y)
  rw [Functor.mem_inheritedTopology_iff_functorPushforward _ _
    (Stack.isFiberedInGroupoids_quotientStack _)] at hy
  rw [Functor.mem_inheritedTopology_iff_functorPushforward _ _
    (isFiberedInGroupoids_cyclicStackModel p 𝒞 hS)]
  refine GrothendieckTopology.superset_covering _ ?_ hy
  rintro W g ⟨Z, a, h, ⟨d⟩, rfl⟩
  refine ⟨ShrinkHoms.toShrinkHoms Z, (ShrinkHoms.functor _).map a, h,
    ⟨{  obj := d.obj
        lift := (ShrinkHoms.functor _).map d.lift
        map := (ShrinkHoms.functor _).map d.map
        fac := ?_ }⟩, ?_⟩
  · change (ShrinkHoms.functor _).map d.lift ≫ (ShrinkHoms.functor _).map d.map = _
    exact ((ShrinkHoms.functor _).map_comp _ _).symm.trans (congrArg _ d.fac)
  · change h ≫ _ = h ≫ (Stack.quotientStack _).p.map ((equivShrink _).symm (equivShrink _ a))
    rw [Equiv.symm_apply_apply]

/-- Pushing a sieve forward along two equal functors gives the same covering condition. -/
private theorem functorPushforward_mem_congr {X D : Type*} [Category X] [Category D]
    {F G : X ⥤ D} (h : F = G) (J : GrothendieckTopology D) {y : X} (R : Sieve y) :
    R.functorPushforward F ∈ J (F.obj y) ↔ R.functorPushforward G ∈ J (G.obj y) := by
  subst h
  rfl

/-- **The inclusion `[S/_p(ℤ/pℤ)] ⥤ [S/(ℤ/pℤ)]` is a dense subsite inclusion** for the two fppf
topologies. -/
instance isDenseSubsite_cyclicPointwiseInclusion :
    (cyclicPointwiseInclusion p 𝒞 hS).IsDenseSubsite (cyclicPointwiseTopology p 𝒞 hS)
      (cyclicStackTopology p 𝒞 hS) :=
  Functor.isDenseSubsite_inheritedTopology (cyclicPointwise p 𝒞 hS).p (𝟭 _)
    (cyclicPointwiseInclusion p 𝒞 hS) (cyclicStackModel p 𝒞 hS).p
    (BigFppfOver.baseOverTopology 𝒞 _ hS .fppf) (BigFppfOver.baseOverTopology 𝒞 _ hS .fppf)
    (isFiberedInGroupoids_cyclicPointwise p 𝒞 hS) (isFiberedInGroupoids_cyclicStackModel p 𝒞 hS)
    { functorPushforward_mem_iff := fun {_ R} => by
        rw [Sieve.functorPushforward_id]; exact Iff.rfl }
    (fun y R => by
      rw [Sieve.functorPushforward_id, ← Sieve.functorPushforward_comp]
      exact functorPushforward_mem_congr (cyclicPointwiseInclusion_comp_p p 𝒞 hS) _ R)
    (isCoverDense_cyclicPointwiseInclusion p 𝒞 hS)

/-- The structure sheaf of rings of `[S/(ℤ/pℤ)]` on its fppf site: the ring sheaf of the modules
`Mod(𝒪_𝒳)` of `AlgebraicGeometry.Stack.fppfModules`. -/
abbrev cyclicStackRing : Sheaf (cyclicStackTopology p 𝒞 hS) RingCat.{u} :=
  FibredSite.ringStructureSheafCore 𝒞 _ hS (cyclicStackModel p 𝒞 hS).p
    (isFiberedInGroupoids_cyclicStackModel p 𝒞 hS) .fppf

/-- The structure sheaf of rings of the pointwise quotient: the restriction of that of
`[S/(ℤ/pℤ)]`. -/
abbrev cyclicPointwiseRing : Sheaf (cyclicPointwiseTopology p 𝒞 hS) RingCat.{u} :=
  Stacks.DenseSubsiteModules.ringRestriction (cyclicPointwiseTopology p 𝒞 hS)
    (cyclicStackTopology p 𝒞 hS) (cyclicPointwiseInclusion p 𝒞 hS) (cyclicStackRing p 𝒞 hS)

/-- **Restriction of modules from `[S/(ℤ/pℤ)]` to the pointwise quotient.** -/
abbrev cyclicPointwiseRestriction :
    SheafOfModules.{u} (cyclicStackRing p 𝒞 hS) ⥤ SheafOfModules.{u} (cyclicPointwiseRing p 𝒞 hS) :=
  Stacks.DenseSubsiteModules.moduleRestriction (cyclicPointwiseTopology p 𝒞 hS)
    (cyclicStackTopology p 𝒞 hS) (cyclicPointwiseInclusion p 𝒞 hS) (cyclicStackRing p 𝒞 hS)

/-- **Restriction of modules from `[S/(ℤ/pℤ)]` to the pointwise quotient is an equivalence**: the
Comparison Lemma for the dense subsite `[S/_p(ℤ/pℤ)] ⥤ [S/(ℤ/pℤ)]`. -/
instance isEquivalence_cyclicPointwiseRestriction :
    (cyclicPointwiseRestriction p 𝒞 hS).IsEquivalence :=
  Stack.FibredDenseSubsite.isEquivalence_moduleRestriction (cyclicStackModel p 𝒞 hS).p
    (isFiberedInGroupoids_cyclicStackModel p 𝒞 hS) (cyclicPointwiseInclusion p 𝒞 hS) _ _ _

/-- The ring of sections at an object of the pointwise quotient is the ring of functions of the
scheme it lies over. -/
theorem cyclicPointwiseRing_obj_obj (x : (cyclicPointwise p 𝒞 hS).obj) :
    (cyclicPointwiseRing p 𝒞 hS).obj.obj (op x) =
      (BigFppfOver.structureSheaf 𝒞 _ hS).obj.obj (op ((cyclicPointwise p 𝒞 hS).p.obj x)) :=
  rfl

/-- The restriction maps of the structure sheaf of the pointwise quotient are those of the
functions on the schemes the objects lie over. -/
theorem cyclicPointwiseRing_obj_map {x y : (cyclicPointwise p 𝒞 hS).obj} (f : x ⟶ y) :
    (cyclicPointwiseRing p 𝒞 hS).obj.map f.op =
      (BigFppfOver.structureSheaf 𝒞 _ hS).obj.map ((cyclicPointwise p 𝒞 hS).p.map f).op := by
  change (BigFppfOver.structureSheaf 𝒞 _ hS).obj.map
    ((cyclicStackModel p 𝒞 hS).p.map ((cyclicPointwiseInclusion p 𝒞 hS).map f)).op = _
  rw [cyclicStackModel_p_map_cyclicPointwiseInclusion_map]
  rfl

/-- The final object `S` of the big fppf site over `S`. -/
abbrev cyclicBaseObject : BigFppfOver 𝒞 (Spec (.of (Polynomial k))) hS :=
  Space.baseTerminal 𝒞 _ hS

/-- `S` is the final object of the big fppf site over `S`. -/
def isTerminalCyclicBaseObject : IsTerminal (cyclicBaseObject 𝒞 hS) :=
  Over.mkIdTerminal

/-- **The object `U` of the pointwise quotient**: the unique point of `S` over the final object
`S` of the site, the trivial torsor. -/
def cyclicPointwiseUnitObject : (cyclicPointwise p 𝒞 hS).obj where
  base := cyclicBaseObject 𝒞 hS
  fiber := (𝟙 (cyclicBaseObject 𝒞 hS) : (yoneda.obj (cyclicBaseObject 𝒞 hS)).obj
    (op (cyclicBaseObject 𝒞 hS)))

/-- The ring `Γ(S, 𝒪_S) = k[x]`, the sections of the structure sheaf of the site at its final
object, read as a commutative ring. -/
abbrev cyclicBaseRing : Type u :=
  ↥((BigFppfOver.structureSheaf 𝒞 (Spec (.of (Polynomial k))) hS).obj.obj
    (op (cyclicBaseObject 𝒞 hS)))

/-- `Γ(S, 𝒪_S)` is commutative. -/
instance : CommRing (cyclicBaseRing 𝒞 hS) :=
  inferInstanceAs (CommRing Γ(Spec (.of (Polynomial k)), ⊤))

/-- The restriction of a function on `S` to an object of the pointwise quotient, along the unique
morphism to the final object. -/
abbrev cyclicBaseRingToSections (x : (cyclicPointwise p 𝒞 hS).obj) :
    cyclicBaseRing 𝒞 hS →+* (cyclicPointwiseRing p 𝒞 hS).obj.obj (op x) :=
  ((BigFppfOver.structureSheaf 𝒞 _ hS).obj.map
    ((isTerminalCyclicBaseObject 𝒞 hS).from
      ((cyclicStackModel p 𝒞 hS).p.obj ((cyclicPointwiseInclusion p 𝒞 hS).obj x))).op).hom

/-- **The ring map `Γ(S, 𝒪_S) ⟶ Γ(𝒫, 𝒪_𝒫)`**: a function on `S` restricts to every object of
the pointwise quotient, compatibly. -/
def cyclicPointwiseBaseRingHom :
    cyclicBaseRing 𝒞 hS →+* GlobalSectionRing (cyclicPointwiseRing p 𝒞 hS) where
  toFun a := ⟨fun x => cyclicBaseRingToSections p 𝒞 hS x.unop a, fun {x y} f => by
    change ((cyclicPointwiseRing p 𝒞 hS).obj.map f).hom
      (cyclicBaseRingToSections p 𝒞 hS x.unop a) = cyclicBaseRingToSections p 𝒞 hS y.unop a
    have hf : ((isTerminalCyclicBaseObject 𝒞 hS).from
        ((cyclicStackModel p 𝒞 hS).p.obj ((cyclicPointwiseInclusion p 𝒞 hS).obj x.unop))).op ≫
          ((cyclicStackModel p 𝒞 hS).p.map ((cyclicPointwiseInclusion p 𝒞 hS).map f.unop)).op =
        ((isTerminalCyclicBaseObject 𝒞 hS).from
          ((cyclicStackModel p 𝒞 hS).p.obj ((cyclicPointwiseInclusion p 𝒞 hS).obj y.unop))).op := by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op ((isTerminalCyclicBaseObject 𝒞 hS).hom_ext _ _)
    change ((BigFppfOver.structureSheaf 𝒞 _ hS).obj.map
      ((cyclicStackModel p 𝒞 hS).p.map ((cyclicPointwiseInclusion p 𝒞 hS).map f.unop)).op).hom
        (((BigFppfOver.structureSheaf 𝒞 _ hS).obj.map ((isTerminalCyclicBaseObject 𝒞 hS).from
          ((cyclicStackModel p 𝒞 hS).p.obj ((cyclicPointwiseInclusion p 𝒞 hS).obj x.unop))).op).hom
            a) = _
    rw [← RingCat.comp_apply, ← Functor.map_comp, hf]
    rfl⟩
  map_one' := Subtype.ext (funext fun x => map_one _)
  map_mul' a b := Subtype.ext (funext fun x => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun x => map_zero _)
  map_add' a b := Subtype.ext (funext fun x => map_add _ _ _)

/-- The component at `x` of the image of `a` under `cyclicPointwiseBaseRingHom` is the restriction
of `a` to `x`. -/
theorem cyclicPointwiseBaseRingHom_apply (a : cyclicBaseRing 𝒞 hS)
    (x : (cyclicPointwise p 𝒞 hS).obj) :
    (cyclicPointwiseBaseRingHom p 𝒞 hS a).1 (op x) = cyclicBaseRingToSections p 𝒞 hS x a :=
  rfl

/-- The restriction of a function on `S` to an object of `[S/(ℤ/pℤ)]`, along the unique morphism
to the final object. -/
abbrev cyclicBaseRingToStackSections (x : (cyclicStackModel p 𝒞 hS).obj) :
    cyclicBaseRing 𝒞 hS →+* (cyclicStackRing p 𝒞 hS).obj.obj (op x) :=
  ((BigFppfOver.structureSheaf 𝒞 _ hS).obj.map
    ((isTerminalCyclicBaseObject 𝒞 hS).from ((cyclicStackModel p 𝒞 hS).p.obj x)).op).hom

/-- **The ring map `Γ(S, 𝒪_S) ⟶ Γ(𝒳, 𝒪_𝒳)`**: a function on `S` restricts to every object of
`[S/(ℤ/pℤ)]`, compatibly. -/
def cyclicStackBaseRingHom :
    cyclicBaseRing 𝒞 hS →+* GlobalSectionRing (cyclicStackRing p 𝒞 hS) where
  toFun a := ⟨fun x => cyclicBaseRingToStackSections p 𝒞 hS x.unop a, fun {x y} f => by
    have hf : ((isTerminalCyclicBaseObject 𝒞 hS).from
        ((cyclicStackModel p 𝒞 hS).p.obj x.unop)).op ≫ ((cyclicStackModel p 𝒞 hS).p.map f.unop).op =
        ((isTerminalCyclicBaseObject 𝒞 hS).from ((cyclicStackModel p 𝒞 hS).p.obj y.unop)).op := by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op ((isTerminalCyclicBaseObject 𝒞 hS).hom_ext _ _)
    change ((BigFppfOver.structureSheaf 𝒞 _ hS).obj.map
      ((cyclicStackModel p 𝒞 hS).p.map f.unop).op).hom
        (((BigFppfOver.structureSheaf 𝒞 _ hS).obj.map ((isTerminalCyclicBaseObject 𝒞 hS).from
          ((cyclicStackModel p 𝒞 hS).p.obj x.unop)).op).hom a) = _
    rw [← RingCat.comp_apply, ← Functor.map_comp, hf]
    rfl⟩
  map_one' := Subtype.ext (funext fun x => map_one _)
  map_mul' a b := Subtype.ext (funext fun x => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun x => map_zero _)
  map_add' a b := Subtype.ext (funext fun x => map_add _ _ _)

/-- The component at `x` of the image of `a` under `cyclicStackBaseRingHom` is the restriction of
`a` to `x`. -/
theorem cyclicStackBaseRingHom_apply (a : cyclicBaseRing 𝒞 hS)
    (x : (cyclicStackModel p 𝒞 hS).obj) :
    (cyclicStackBaseRingHom p 𝒞 hS a).1 (op x) = cyclicBaseRingToStackSections p 𝒞 hS x a :=
  rfl

/-- The final object `S → S` of the total category of the base `S`, regarded as an algebraic
stack over itself. -/
abbrev cyclicBaseStackTerminal : Over (cyclicBaseObject 𝒞 hS) :=
  Over.mk (𝟙 (cyclicBaseObject 𝒞 hS))

/-- **The global sections of the direct image `Γ(S, f_* -)`** along `f : [S/(ℤ/pℤ)] ⟶ S`: the
direct image of modules at the universe of the schemes, evaluated at the final object of the
total category of `S`, as modules over `Γ(S, 𝒪_S)`. -/
abbrev cyclicPushforwardSections.{w} :
    Stack.fppfModules 𝒞 _ hS (cyclicClassifyingStack.{u, w} p 𝒞 hS) ⥤
      ModuleCat.{u} ((FibredSite.ringStructureSheafCore 𝒞 _ hS (baseStack.{u, w} 𝒞 hS).val.val.p
        (baseStack.{u, w} 𝒞 hS).val.isFiberedInGroupoids .fppf).obj.obj
          (op (cyclicBaseStackTerminal 𝒞 hS : (baseStack.{u, w} 𝒞 hS).val.val.obj))) :=
  Stack.fppfModulesPushforward 𝒞 _ hS (cyclicStructureMorphism.{u, w} p 𝒞 hS) ⋙
    SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _
      (op (cyclicBaseStackTerminal 𝒞 hS : (baseStack.{u, w} 𝒞 hS).val.val.obj))

end Stacks.Examples.UnboundedDerivedPushforward

namespace AlgebraicGeometry.Stack

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall

/-- The sections at an object of the direct image of modules along a `1`-morphism of algebraic
stacks depend additively on the module. -/
theorem fppfModulesPushforward_comp_evaluation_additive.{w} {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (y : 𝒴.val.val.obj) :
    (fppfModulesPushforward B S hS f ⋙ SheafOfModules.forget _ ⋙
      PresheafOfModules.evaluation _ (op y)).Additive :=
  inferInstance

end AlgebraicGeometry.Stack

namespace Stacks.Examples.UnboundedDerivedPushforward

variable (p : ℕ) [NeZero p] {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- `Γ(S, f_* -)` is additive. -/
instance cyclicPushforwardSections_additive.{w} :
    (cyclicPushforwardSections.{u, w} p 𝒞 hS).Additive :=
  Stack.fppfModulesPushforward_comp_evaluation_additive _ _

end Stacks.Examples.UnboundedDerivedPushforward
