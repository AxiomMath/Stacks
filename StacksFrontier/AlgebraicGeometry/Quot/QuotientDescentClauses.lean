module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientRestrictOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcDescentTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackAlongFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of quasi-coherent quotients along fpqc coverings

Facts about quasi-coherent modules on algebraic spaces and their fpqc descent: kernels of
quasi-coherent quotients are quasi-coherent, a homomorphism of quasi-coherent modules vanishing
along an fpqc covering is zero, quasi-coherent quotients descend along fpqc coverings
(Stacks 08IU), and flatness over the base and finite presentation descend along fpqc coverings.

## Main results

* `AlgebraicGeometry.Space.kernelQuasicoherent`: the kernel of a quotient of a quasi-coherent
  module with quasi-coherent quotient module is quasi-coherent (the kernel clause of
  Stacks 03M1).
* `AlgebraicGeometry.Space.reflectsZeroAlongFpqcCovering`: a homomorphism of quasi-coherent
  modules whose inverse images along an fpqc covering vanish is zero (the faithfulness clause of
  Stacks 04W8), an alias of
  `AlgebraicGeometry.Space.modulePullback_reflectsZero_of_isFpqcCovering`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.quotientDatum`: quotients of the
  components of a descent datum, compatible with its pairwise isomorphisms, form a descent datum.
* `AlgebraicGeometry.Space.exists_quotientRestrict_eq_of_isFpqcCovering`: **fpqc descent of
  quasi-coherent quotients** of a quasi-coherent module, from Stacks 04W8 (effectivity and full
  faithfulness) and the vanishing of the cokernel of the descended homomorphism.
* `AlgebraicGeometry.Space.bijOn_quotientRestrict_of_isFpqcCovering`: **Stacks 08IU**, the
  bijection between quasi-coherent quotients of `F` and families of quasi-coherent quotients on an
  fpqc covering which agree on fpqc coverings of the pairwise fibre products.
* `AlgebraicGeometry.Space.descendsQuotientsAlongFpqcCovering_of_isQuasicoherentOnSite` and its
  primed form: the conclusion of `AlgebraicGeometry.Space.DescendsQuotientsAlongFpqcCovering`
  for a module whose inverse image (respectively, which) is quasi-coherent.

## Implementation notes

A quotient `F ⟶ Q` is recorded by its kernel, a subobject of `F`, as in Situation 082M.  The
descent of a compatible family of quotients goes through epimorphisms rather than through
subobjects: two quotients of one module with the same kernel are identified under the module
(`CategoryTheory.Limits.isoOfKernelSubobjectEq`), which turns the agreement of a family on the
pairwise fibre products into pairwise isomorphisms of the quotients, and the cocycle condition of
those isomorphisms is the cocycle condition of the canonical descent datum of the module read
through the epimorphisms.

`AlgebraicGeometry.Space.DescendsQuotientsAlongFpqcCovering` quantifies over every module `F`,
quasi-coherent or not; Stacks 08IU and Stacks 04W8 are statements about quasi-coherent modules,
and its conclusion is proved here under quasi-coherence of the module being descended.

Two local instance priorities are raised: the abelian structure of sheaves of modules and its
kernels and cokernels, and epimorphisms and monomorphisms out of isomorphisms.  Without them
instance search reaches instances of the import closure at other module universes first and
stops at an unsolvable universe constraint.

## References

* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- If the kernel of `p` is contained in the kernel of `p'`, then `p'` kills the kernel of
`p`. -/
theorem kernel_ι_comp_eq_zero_of_kernelSubobject_le {A Q Q' : C} (p : A ⟶ Q) (p' : A ⟶ Q')
    (h : kernelSubobject p ≤ kernelSubobject p') : kernel.ι p ≫ p' = 0 := by
  rw [← kernelSubobject_arrow' p, ← Subobject.ofLE_arrow h, Category.assoc, Category.assoc,
    kernelSubobject_arrow_comp, comp_zero, comp_zero]

/-- **Two quotients of one object with the same kernel are canonically isomorphic**: for
epimorphisms `p : A ⟶ Q` and `p' : A ⟶ Q'` with equal kernels, the isomorphism `Q ≅ Q'` under
`A`. -/
noncomputable def isoOfKernelSubobjectEq {A Q Q' : C} (p : A ⟶ Q) (p' : A ⟶ Q') [Epi p]
    [Epi p'] (h : kernelSubobject p = kernelSubobject p') : Q ≅ Q' where
  hom := Abelian.epiDesc p p' (kernel_ι_comp_eq_zero_of_kernelSubobject_le p p' h.le)
  inv := Abelian.epiDesc p' p (kernel_ι_comp_eq_zero_of_kernelSubobject_le p' p h.ge)
  hom_inv_id := by
    rw [← cancel_epi p, Abelian.comp_epiDesc_assoc, Abelian.comp_epiDesc, Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi p', Abelian.comp_epiDesc_assoc, Abelian.comp_epiDesc, Category.comp_id]

/-- The isomorphism of two quotients with the same kernel is an isomorphism under `A`. -/
@[reassoc (attr := simp)]
theorem comp_isoOfKernelSubobjectEq_hom {A Q Q' : C} (p : A ⟶ Q) (p' : A ⟶ Q') [Epi p]
    [Epi p'] (h : kernelSubobject p = kernelSubobject p') :
    p ≫ (isoOfKernelSubobjectEq p p' h).hom = p' :=
  Abelian.comp_epiDesc _ _ _

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]


end SheafOfModules

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type v} {X : AlgebraicSpaces B S hS} {Y : I → AlgebraicSpaces B S hS}
  {f : ∀ i, Y i ⟶ X}

/-- A pairwise isomorphism read on a test space is natural in a family of morphisms commuting
with two families of pairwise isomorphisms, neither of which is asked to satisfy the cocycle
condition. -/
theorem transitionOn_naturality_of_family
    {F F' : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2}
    {φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j)}
    {φ' : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F' i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F' j)}
    (a : ∀ i, F i ⟶ F' i)
    (ha : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).map (a i) ≫ (φ' i j).hom =
      (φ i j).hom ≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).map (a j))
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) :
    (modulePullback B S hS vi).map (a i) ≫
        (transitionOn B S hS Y f F' φ' i j v vi vj hi hj).hom =
      (transitionOn B S hS Y f F φ i j v vi vj hi hj).hom ≫
        (modulePullback B S hS vj).map (a j) := by
  subst hi hj
  simp only [transitionOn, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, pullbackComparison_naturality, Category.assoc]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, ha, Functor.map_comp, Category.assoc,
    pullbackComparison_inv_naturality]

/-- **The quotient of a descent datum.**  Given a descent datum `D`, quasi-coherent quotients
`π i : D.F i ⟶ Q i` and isomorphisms `φ i j` of the two inverse images of the quotients on the
pairwise fibre products under the pairwise isomorphisms of `D`, the quotients form a descent
datum: its cocycle condition is that of `D`, read through the epimorphisms `π i`. -/
def DescentDatum.quotientDatum (D : DescentDatum B S hS Y f)
    (Q : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2) (hQ : ∀ i, (Q i).IsQuasicoherentOnSite)
    (π : ∀ i, D.F i ⟶ Q i) (hπ : ∀ i, Epi (π i))
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (Q i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (Q j))
    (hφ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).map (π i) ≫ (φ i j).hom =
      (D.transition i j).hom ≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).map (π j)) :
    DescentDatum B S hS Y f where
  F := Q
  quasicoherent := hQ
  transition := φ
  cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ := by
    have := hπ i
    apply Iso.ext
    rw [← cancel_epi ((modulePullback B S hS vi).map (π i))]
    have hD := congrArg Iso.hom
      (D.cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁)
    rw [Iso.trans_hom] at hD
    rw [Iso.trans_hom, ← Category.assoc, transitionOn_naturality_of_family π hφ,
      Category.assoc, transitionOn_naturality_of_family π hφ, ← Category.assoc, hD,
      transitionOn_naturality_of_family π hφ]

/-- The projection of a descent datum onto its quotient, as a morphism of descent data. -/
def DescentDatum.quotientHom (D : DescentDatum B S hS Y f)
    (Q : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2) (hQ : ∀ i, (Q i).IsQuasicoherentOnSite)
    (π : ∀ i, D.F i ⟶ Q i) (hπ : ∀ i, Epi (π i))
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (Q i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (Q j))
    (hφ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).map (π i) ≫ (φ i j).hom =
      (D.transition i j).hom ≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).map (π j)) :
    D ⟶ D.quotientDatum Q hQ π hπ φ hφ :=
  DescentDatum.Hom.mk π hφ

/-- The component of `DescentDatum.quotientHom` at `i` is the quotient map `π i`. -/
@[simp]
theorem DescentDatum.quotientHom_app (D : DescentDatum B S hS Y f)
    (Q : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2) (hQ : ∀ i, (Q i).IsQuasicoherentOnSite)
    (π : ∀ i, D.F i ⟶ Q i) (hπ : ∀ i, Epi (π i))
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (Q i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (Q j))
    (hφ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).map (π i) ≫ (φ i j).hom =
      (D.transition i j).hom ≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).map (π j))
    (i : I) : (D.quotientHom Q hQ π hπ φ hφ).app i = π i :=
  rfl

end AlgebraicGeometry.Space.QuasiCoherentDescent

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The kernel clause of Stacks 03M1.**  The kernel of a quotient `M ⟶ M/K` of a quasi-coherent
module whose quotient module is quasi-coherent is quasi-coherent: `K` is the kernel of the
projection `M ⟶ M/K`, and quasi-coherence on the small étale site of an algebraic space is closed
under kernels. -/
theorem kernelQuasicoherent : KernelQuasicoherent B S hS := by
  intro W M hM K hQ
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS W.1 W.2
  exact ObjectProperty.prop_of_isLimit_kernelFork _
    (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel K.arrow)) hM hQ

/-- **The faithfulness clause of Stacks 04W8, read on one homomorphism.**  A homomorphism of
quasi-coherent modules whose inverse images along every member of an fpqc covering vanish is
zero.

The proof is `AlgebraicGeometry.Space.modulePullback_reflectsZero_of_isFpqcCovering`, which
lives with the statements that consume the clause, in
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorDescent.lean`; this name is kept for the
statements that refer to the clause by the name of its predicate. -/
alias reflectsZeroAlongFpqcCovering := modulePullback_reflectsZero_of_isFpqcCovering

/-! ### Translating between the forms of the restriction of a quotient -/

/-- The comparison of Stacks 03LU at a factorization, read on one module, is the comparison
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison`. -/
theorem modulePullbackTriangle_app_eq_pullbackComparison {A P T : AlgebraicSpaces B S hS}
    (g : T ⟶ P) (q : P ⟶ A) (v : T ⟶ A) (hv : g ≫ q = v) (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullbackTriangle B S hS hv).app M =
      QuasiCoherentDescent.pullbackComparison B S hS g q v hv M := by
  subst hv
  rw [QuasiCoherentDescent.pullbackComparison_rfl, modulePullbackTriangle_rfl]
  rfl

/-- **The canonical comparison of two inverse images is the comparison of two factorizations.**
At a common factorization `d` of `a ≫ fi` and of `b ≫ fj`, the canonical comparison of Stacks
04W5 is the inverse of the comparison of Stacks 03LU for `a` followed by the one for `b`. -/
theorem modulePullbackTriangle_symm_trans_eq_canonicalComparison
    {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q) (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A)
    (h : a ≫ fi = b ≫ fj) {d : P ⟶ A} (ha : a ≫ fi = d) (hb : b ≫ fj = d)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    ((modulePullbackTriangle B S hS ha).app M).symm ≪≫ (modulePullbackTriangle B S hS hb).app M =
      QuasiCoherentDescent.canonicalComparison a b fi fj h M := by
  rw [modulePullbackTriangle_app_eq_pullbackComparison,
    modulePullbackTriangle_app_eq_pullbackComparison,
    QuasiCoherentDescent.canonicalComparison_eq_pullbackComparison B S hS a b fi fj h d ha hb]

/-- **Restricting the restriction of a quotient.**  Restricting along `g` over `X` the
restriction of a quotient of `F` along `a` is restricting it along `g ≫ a`. -/
theorem quotientRestrictOver_quotientRestrict {X W W' : AlgebraicSpaces B S hS} {a : W ⟶ X}
    {a' : W' ⟶ X} (g : W' ⟶ W) (h : g ≫ a = a') (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject F) :
    quotientRestrictOver g h F (quotientRestrict a K) = quotientRestrict a' K := by
  have hc : (modulePullback B S hS a').map (cokernel.π K.arrow) ≫
      ((modulePullbackTriangle B S hS h).hom.app (cokernel K.arrow) ≫
        (modulePullback B S hS g).map (quotientRestrictCokernelIso a K).inv) =
      Functor.conjQuotientProjection (modulePullbackTriangle B S hS h) (quotientRestrict a K) := by
    rw [Functor.conjQuotientProjection, ← cokernel_π_comp_quotientRestrictCokernelIso_inv,
      Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (modulePullbackTriangle B S hS h).hom.naturality (cokernel.π K.arrow)
  exact kernelSubobject_eq_of_comp_mono _ _ _ hc

/-- **Restriction of a quotient commutes with transport along an isomorphism.** -/
theorem quotientRestrict_quotientTransport {X W : AlgebraicSpaces B S hS} (g : W ⟶ X)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (ι : F' ≅ F) (K : Subobject F) :
    quotientRestrict g (quotientTransport ι K) =
      quotientTransport ((modulePullback B S hS g).mapIso ι) (quotientRestrict g K) := by
  have h₁ : ((modulePullback B S hS g).map ι.hom ≫
        (modulePullback B S hS g).map (cokernel.π K.arrow)) ≫
      (modulePullback B S hS g).map (quotientTransportCokernelIso ι K).inv =
      (modulePullback B S hS g).map (cokernel.π (quotientTransport ι K).arrow) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← comp_quotientTransportCokernelIso_inv]
  have h₂ : ((modulePullback B S hS g).map ι.hom ≫
        (modulePullback B S hS g).map (cokernel.π K.arrow)) ≫
      (quotientRestrictCokernelIso g K).inv =
      ((modulePullback B S hS g).mapIso ι).hom ≫ cokernel.π (quotientRestrict g K).arrow := by
    rw [Category.assoc, cokernel_π_comp_quotientRestrictCokernelIso_inv]
    rfl
  exact (kernelSubobject_eq_of_comp_mono _ _ _ h₁).trans
    (kernelSubobject_eq_of_comp_mono _ _ _ h₂).symm

/-- The two composites `X ijk ⟶ X i ×_X X j ⟶ X i ⟶ X` and `X ijk ⟶ X i ×_X X j ⟶ X j ⟶ X`
agree. -/
theorem pair_comp_condition {I : Type v} {X : AlgebraicSpaces B S hS}
    {Xi : I → AlgebraicSpaces B S hS} (f : ∀ i, Xi i ⟶ X) (i j : I) {T : AlgebraicSpaces B S hS}
    (g : T ⟶ QuasiCoherentDescent.pair B S hS Xi f i j) :
    (g ≫ QuasiCoherentDescent.pairSnd B S hS Xi f i j) ≫ f j =
      (g ≫ QuasiCoherentDescent.pairFst B S hS Xi f i j) ≫ f i := by
  rw [Category.assoc, Category.assoc, QuasiCoherentDescent.pair_condition]

/-- **Fpqc descent of quasi-coherent quotients, in the canonical form.**  Let `G` be a
quasi-coherent module on `W`, let `{p i : Z i ⟶ W}` be an fpqc covering and let `K i` be
quotients of `p i ^* G` with quasi-coherent quotient modules which agree on the pairwise fibre
products `Z i ×_W Z j`, read through the canonical comparison of the two inverse images of `G`
there.  Then there is a quotient of `G` with quasi-coherent quotient module restricting to `K i`
along every `p i`.

The quotients and the pairwise identifications of their inverse images form a descent datum,
which is effective by Stacks 04W8; the family of projections is a morphism of descent data out
of the canonical descent datum of `G`, so it descends by the fullness clause of Stacks 04W8 to
a homomorphism `G ⟶ N`; that homomorphism is surjective because its cokernel is quasi-coherent
and is killed by the covering. -/
@[sga "1 VIII 1.8" "Existence clause"]
theorem exists_quotientRestrict_eq_of_isFpqcCovering {I : Type v} {W : AlgebraicSpaces B S hS}
    {Z : I → AlgebraicSpaces B S hS} (p : ∀ i, Z i ⟶ W)
    (hp : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    (G : Modules.{u, u} B S hS W.1 W.2) (hG : G.IsQuasicoherentOnSite)
    (K : ∀ i, Subobject ((modulePullback B S hS (p i)).obj G))
    (hK : ∀ i, (cokernel (K i).arrow).IsQuasicoherentOnSite)
    (hcompat : ∀ i j, quotientRestrict (QuasiCoherentDescent.pairFst B S hS Z p i j) (K i) =
      quotientTransport (QuasiCoherentDescent.canonicalComparison
          (QuasiCoherentDescent.pairFst B S hS Z p i j)
          (QuasiCoherentDescent.pairSnd B S hS Z p i j) (p i) (p j)
          (QuasiCoherentDescent.pair_condition B S hS Z p i j) G)
        (quotientRestrict (QuasiCoherentDescent.pairSnd B S hS Z p i j) (K j))) :
    ∃ K₀ : Subobject G, (cokernel K₀.arrow).IsQuasicoherentOnSite ∧
      ∀ i, quotientRestrict (p i) K₀ = K i := by
  classical
  have hker : ∀ i j, kernelSubobject ((modulePullback B S hS
        (QuasiCoherentDescent.pairFst B S hS Z p i j)).map (cokernel.π (K i).arrow)) =
      kernelSubobject ((QuasiCoherentDescent.canonicalComparison
          (QuasiCoherentDescent.pairFst B S hS Z p i j)
          (QuasiCoherentDescent.pairSnd B S hS Z p i j) (p i) (p j)
          (QuasiCoherentDescent.pair_condition B S hS Z p i j) G).hom ≫ (modulePullback B S hS
        (QuasiCoherentDescent.pairSnd B S hS Z p i j)).map (cokernel.π (K j).arrow)) := by
    intro i j
    refine (hcompat i j).trans ?_
    refine kernelSubobject_eq_of_comp_mono _ _
      (quotientRestrictCokernelIso (QuasiCoherentDescent.pairSnd B S hS Z p i j) (K j)).inv ?_
    rw [Category.assoc, cokernel_π_comp_quotientRestrictCokernelIso_inv]
  have hepi : ∀ i j, Epi ((QuasiCoherentDescent.canonicalComparison
          (QuasiCoherentDescent.pairFst B S hS Z p i j)
          (QuasiCoherentDescent.pairSnd B S hS Z p i j) (p i) (p j)
          (QuasiCoherentDescent.pair_condition B S hS Z p i j) G).hom ≫ (modulePullback B S hS
        (QuasiCoherentDescent.pairSnd B S hS Z p i j)).map (cokernel.π (K j).arrow)) :=
    fun i j ↦ epi_comp _ _
  have hπ : ∀ i, Epi (cokernel.π (K i).arrow) := fun _ ↦ coequalizer.π_epi
  obtain ⟨φ, hφ⟩ : ∃ φ : ∀ i j, (modulePullback B S hS
        (QuasiCoherentDescent.pairFst B S hS Z p i j)).obj (cokernel (K i).arrow) ≅
        (modulePullback B S hS (QuasiCoherentDescent.pairSnd B S hS Z p i j)).obj
          (cokernel (K j).arrow),
      ∀ i j, (modulePullback B S hS (QuasiCoherentDescent.pairFst B S hS Z p i j)).map
        (cokernel.π (K i).arrow) ≫ (φ i j).hom =
      (QuasiCoherentDescent.canonicalComparison
          (QuasiCoherentDescent.pairFst B S hS Z p i j)
          (QuasiCoherentDescent.pairSnd B S hS Z p i j) (p i) (p j)
          (QuasiCoherentDescent.pair_condition B S hS Z p i j) G).hom ≫ (modulePullback B S hS
        (QuasiCoherentDescent.pairSnd B S hS Z p i j)).map (cokernel.π (K j).arrow) :=
    ⟨fun i j ↦ @isoOfKernelSubobjectEq _ _ _ _ _ _ _ _ inferInstance (hepi i j) (hker i j),
      fun i j ↦ @comp_isoOfKernelSubobjectEq_hom _ _ _ _ _ _ _ _ inferInstance (hepi i j)
        (hker i j)⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := QuasiCoherentDescent.forall_isEffective_of_isFpqcCovering B S hS Z p hp
    ((QuasiCoherentDescent.canonicalDescentDatum' B S hS Z p G hG).quotientDatum
      (fun i ↦ cokernel (K i).arrow) hK (fun i ↦ cokernel.π (K i).arrow) hπ φ hφ)
  have := QuasiCoherentDescent.full_canonicalDescentFunctor_of_isFpqcCovering'.{u, v}
    B S hS Z p hp
  let χ : (QuasiCoherentDescent.canonicalDescentFunctor' B S hS Z p).obj ⟨G, hG⟩ ⟶
      (QuasiCoherentDescent.canonicalDescentFunctor' B S hS Z p).obj ⟨N, hN⟩ :=
    (QuasiCoherentDescent.canonicalDescentDatum' B S hS Z p G hG).quotientHom _ hK _ hπ φ hφ ≫
      e.hom
  let ε : ∀ i, cokernel (K i).arrow ⟶ (modulePullback B S hS (p i)).obj N := fun i ↦ e.hom.app i
  have hεiso : ∀ i, IsIso (ε i) := fun i ↦
    (QuasiCoherentDescent.DescentDatum.appIso B S hS e i).isIso_hom
  have hεepi : ∀ i, Epi (cokernel.π (K i).arrow ≫ ε i) := fun i ↦
    @epi_comp _ _ _ _ _ _ (hπ i) _ (@IsIso.epi_of_iso _ _ _ _ _ (hεiso i))
  have hεker : ∀ i, kernelSubobject (cokernel.π (K i).arrow ≫ ε i) = K i := fun i ↦ by
    have := hεiso i
    exact (kernelSubobject_comp_mono _ _).trans (kernelSubobject_cokernel_π (K i))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : G ⟶ N, ∀ i,
      (modulePullback B S hS (p i)).map ψ = cokernel.π (K i).arrow ≫ ε i :=
    ⟨((QuasiCoherentDescent.canonicalDescentFunctor' B S hS Z p).preimage χ).hom,
      fun i ↦ congrArg (fun b ↦ b.app i)
        ((QuasiCoherentDescent.canonicalDescentFunctor' B S hS Z p).map_preimage χ)⟩
  clear_value ε
  have : Epi ψ := by
    have := isClosedUnderCokernels_quasicoherentSheaves B S hS W.1 W.2
    have hC : (cokernel ψ).IsQuasicoherentOnSite := ObjectProperty.prop_cokernel _ ψ hG hN
    refine Preadditive.epi_of_cokernel_zero (reflectsZeroAlongFpqcCovering.{u, v} p hp N
      (cokernel ψ) hN hC (cokernel.π ψ) fun i ↦ ?_)
    have : Epi ((modulePullback B S hS (p i)).map ψ) := by rw [hψ i]; exact hεepi i
    rw [← cancel_epi ((modulePullback B S hS (p i)).map ψ), ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, comp_zero]
  refine ⟨kernelSubobject ψ, SheafOfModules.IsQuasicoherentOnSite.of_iso
    (Abelian.cokernelKernelSubobjectIso ψ).symm hN, fun i ↦ ?_⟩
  have h1 : quotientRestrict (p i) (kernelSubobject ψ) =
      kernelSubobject ((modulePullback B S hS (p i)).map ψ) := by
    have hc : (modulePullback B S hS (p i)).map ψ ≫
        (modulePullback B S hS (p i)).map (Abelian.cokernelKernelSubobjectIso ψ).inv =
        (modulePullback B S hS (p i)).map (cokernel.π (kernelSubobject ψ).arrow) := by
      rw [← Functor.map_comp, Abelian.cokernelKernelSubobjectIso_inv_comp]
    exact kernelSubobject_eq_of_comp_mono _ _ _ hc
  rw [h1, hψ i, hεker i]

/-- A quotient restricted along `g` is the transport of its restriction over the base. -/
private theorem quotientRestrict_eq_quotientTransport_quotientRestrictOver
    {X W W' : AlgebraicSpaces B S hS} {a : W ⟶ X} {a' : W' ⟶ X} (g : W' ⟶ W) (h : g ≫ a = a')
    (F : Modules.{u, u} B S hS X.1 X.2) (K : Subobject ((modulePullback B S hS a).obj F)) :
    quotientRestrict g K = quotientTransport ((modulePullbackTriangle B S hS h).app F).symm
      (quotientRestrictOver g h F K) := by
  rw [quotientRestrictOver_eq_quotientTransport, quotientTransport_symm_quotientTransport]

/-- The quotient by a restricted subobject is quasi-coherent when the original quotient is. -/
private theorem isQuasicoherentOnSite_cokernel_quotientRestrictOver'
    {X W W' : AlgebraicSpaces B S hS} {a : W ⟶ X} {a' : W' ⟶ X} (g : W' ⟶ W) (h : g ≫ a = a')
    (F : Modules.{u, u} B S hS X.1 X.2) {K : Subobject ((modulePullback B S hS a).obj F)}
    (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    (cokernel (quotientRestrictOver g h F K).arrow).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (quotientRestrictOverCokernelIso g h F K).symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hK)

/-- **Agreement on a refining covering is agreement on the fibre product.**  Two quotients of
`f i ^* F` and `f j ^* F` whose restrictions to the members of an fpqc covering
`{X ijk ⟶ X i ×_X X j}` agree restrict to the same quotient of the inverse image of `F` to
`X i ×_X X j`, read through the canonical comparison of the two inverse images there.

This is the first step of Remark 08IU, by the full faithfulness in Stacks 04W8: the quotients
are compared through their kernels, which are quasi-coherent. -/
theorem quotientRestrict_pairFst_eq_of_refinement {I : Type v} {J : Type w}
    {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS} (f : ∀ i, Xi i ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (i j : I)
    {Xk : J → AlgebraicSpaces B S hS} (g : ∀ k, Xk k ⟶ QuasiCoherentDescent.pair B S hS Xi f i j)
    (hg : IsFpqcCovering B S hS fun k ↦ (g k).hom)
    (Ki : Subobject ((modulePullback B S hS (f i)).obj F))
    (Kj : Subobject ((modulePullback B S hS (f j)).obj F))
    (hKi : (cokernel Ki.arrow).IsQuasicoherentOnSite)
    (hKj : (cokernel Kj.arrow).IsQuasicoherentOnSite)
    (h : ∀ k, quotientRestrictOver (g k ≫ QuasiCoherentDescent.pairFst B S hS Xi f i j) rfl F Ki =
      quotientRestrictOver (g k ≫ QuasiCoherentDescent.pairSnd B S hS Xi f i j)
        (pair_comp_condition f i j (g k)) F Kj) :
    quotientRestrict (QuasiCoherentDescent.pairFst B S hS Xi f i j) Ki =
      quotientTransport (QuasiCoherentDescent.canonicalComparison
          (QuasiCoherentDescent.pairFst B S hS Xi f i j)
          (QuasiCoherentDescent.pairSnd B S hS Xi f i j) (f i) (f j)
          (QuasiCoherentDescent.pair_condition B S hS Xi f i j) F)
        (quotientRestrict (QuasiCoherentDescent.pairSnd B S hS Xi f i j) Kj) := by
  have hc := modulePushforwardCoherence B S hS
  have hd : QuasiCoherentDescent.pairSnd B S hS Xi f i j ≫ f j =
      QuasiCoherentDescent.pairFst B S hS Xi f i j ≫ f i :=
    (QuasiCoherentDescent.pair_condition B S hS Xi f i j).symm
  have hdF : ((modulePullback B S hS
      (QuasiCoherentDescent.pairFst B S hS Xi f i j ≫ f i)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F hF
  have hQi := isQuasicoherentOnSite_cokernel_quotientRestrictOver'
    (QuasiCoherentDescent.pairFst B S hS Xi f i j) rfl F hKi
  have hQj := isQuasicoherentOnSite_cokernel_quotientRestrictOver'
    (QuasiCoherentDescent.pairSnd B S hS Xi f i j) hd F hKj
  have hAB : quotientRestrictOver (QuasiCoherentDescent.pairFst B S hS Xi f i j) rfl F Ki =
      quotientRestrictOver (QuasiCoherentDescent.pairSnd B S hS Xi f i j) hd F Kj := by
    refine eq_of_quotientRestrictOver_eq reflectsZeroAlongFpqcCovering.{u, w} g
      (fun k ↦ (Category.assoc _ _ _).symm) hg F (kernelQuasicoherent _ hdF _ hQi)
      (kernelQuasicoherent _ hdF _ hQj) hQi hQj fun k ↦ ?_
    rw [quotientRestrictOver_comp hc rfl rfl _ rfl, quotientRestrictOver_comp hc rfl hd _
      (pair_comp_condition f i j (g k))]
    exact h k
  calc quotientRestrict (QuasiCoherentDescent.pairFst B S hS Xi f i j) Ki
      = quotientTransport ((modulePullbackTriangle B S hS
          (rfl : QuasiCoherentDescent.pairFst B S hS Xi f i j ≫ f i = _)).app F).symm
          (quotientRestrictOver (QuasiCoherentDescent.pairFst B S hS Xi f i j) rfl F Ki) :=
        quotientRestrict_eq_quotientTransport_quotientRestrictOver _ _ F Ki
    _ = quotientTransport ((modulePullbackTriangle B S hS
          (rfl : QuasiCoherentDescent.pairFst B S hS Xi f i j ≫ f i = _)).app F).symm
          (quotientTransport ((modulePullbackTriangle B S hS hd).app F)
            (quotientRestrict (QuasiCoherentDescent.pairSnd B S hS Xi f i j) Kj)) := by
        rw [hAB, quotientRestrictOver_eq_quotientTransport]
    _ = _ := by
        rw [quotientTransport_trans, modulePullbackTriangle_symm_trans_eq_canonicalComparison]

/-- **Stacks 08IU.**  Let `X` be an algebraic space over a scheme `S` of a big fppf site, let
`F` be a quasi-coherent `𝒪_X`-module, let `{f i : X i ⟶ X}` be an fpqc covering and for each
`i, j` let `{g i j k : X ijk ⟶ X i ×_X X j}` be an fpqc covering.  Then restriction along the
members of the covering is a bijection from the quotients `F ⟶ Q` with `Q` quasi-coherent onto
the families of quotients `f i ^* F ⟶ Q i` with `Q i` quasi-coherent such that `Q i` and `Q j`
restrict to the same quotient on every `X ijk`.

A quotient is recorded by its kernel, a subobject of the module, as in Situation 082M; the
restriction of a quotient of `F` along `f i` is `AlgebraicGeometry.Space.quotientRestrict`, and
the restrictions of `Q i` and `Q j` to `X ijk` are compared as quotients of the single inverse
image of `F` along `X ijk ⟶ X`, through `AlgebraicGeometry.Space.quotientRestrictOver`.

Injectivity is the faithfulness clause of Stacks 04W8 applied to the kernels, which are
quasi-coherent.  For surjectivity, agreement on the `X ijk` gives agreement on `X i ×_X X j`
(`AlgebraicGeometry.Space.quotientRestrict_pairFst_eq_of_refinement`), and the family descends
by `AlgebraicGeometry.Space.exists_quotientRestrict_eq_of_isFpqcCovering`. -/
@[stacks 08IU, sga "1 VIII 1.8" "more general"]
theorem bijOn_quotientRestrict_of_isFpqcCovering {I : Type v} {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    {Xi : I → AlgebraicSpaces B S hS} (f : ∀ i, Xi i ⟶ X)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    {J : I → I → Type w} {Xijk : ∀ i j, J i j → AlgebraicSpaces B S hS}
    (g : ∀ i j k, Xijk i j k ⟶ QuasiCoherentDescent.pair B S hS Xi f i j)
    (hg : ∀ i j, IsFpqcCovering B S hS fun k ↦ (g i j k).hom) :
    Set.BijOn (fun (K : Subobject F) i ↦ quotientRestrict (f i) K)
      {K | (cokernel K.arrow).IsQuasicoherentOnSite}
      {Q | (∀ i, (cokernel (Q i).arrow).IsQuasicoherentOnSite) ∧
        ∀ i j k, quotientRestrictOver (g i j k ≫ QuasiCoherentDescent.pairFst B S hS Xi f i j)
            rfl F (Q i) =
          quotientRestrictOver (g i j k ≫ QuasiCoherentDescent.pairSnd B S hS Xi f i j)
            (pair_comp_condition f i j (g i j k)) F (Q j)} := by
  refine ⟨fun K hK ↦ ⟨fun i ↦ ?_, fun i j k ↦ ?_⟩, fun K hK K' hK' h ↦ ?_, fun Q hQ ↦ ?_⟩
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso (quotientRestrictCokernelIso (f i) K).symm
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (f i) _ hK)
  · rw [quotientRestrictOver_quotientRestrict, quotientRestrictOver_quotientRestrict]
  · exact eq_of_quotientRestrict_eq f hf
      (kernelQuasicoherent F hF K hK) (kernelQuasicoherent F hF K' hK') hK hK'
      fun i ↦ congrFun h i
  · obtain ⟨K₀, hK₀, hres⟩ := exists_quotientRestrict_eq_of_isFpqcCovering f hf F hF Q hQ.1
      fun i j ↦ quotientRestrict_pairFst_eq_of_refinement f F hF i j (g i j) (hg i j) (Q i) (Q j)
        (hQ.1 i) (hQ.1 j) (hQ.2 i j)
    exact ⟨K₀, hK₀, funext hres⟩

/-- The comparisons of Stacks 03LU for a member of a covering of `W` and for a pairwise fibre
product, composed, are the comparison for the composite through the canonical one.  This is the
associativity coherence of Stacks 03LU, read on one module. -/
theorem modulePullbackTriangle_app_trans_mapIso {V W X Z : AlgebraicSpaces B S hS}
    {f : V ⟶ W} {g : W ⟶ X} {p : X ⟶ Z} {k : V ⟶ X} {q : W ⟶ Z} {r : V ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackTriangle B S hS hr).app M ≪≫
        (modulePullback B S hS f).mapIso ((modulePullbackTriangle B S hS hq).app M) =
      (modulePullbackTriangle B S hS hkr).app M ≪≫
        (modulePullbackTriangle B S hS hk).app ((modulePullback B S hS p).obj M) := by
  have h := congrArg (fun e ↦ e.hom.app M)
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp hk hq hr hkr)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at h
  exact Iso.ext h.symm

/-- **Fpqc descent of quasi-coherent quotients along a covering of an algebraic space over `X`**,
in the shape of `AlgebraicGeometry.Space.DescendsQuotientsAlongFpqcCovering`, for a module whose
inverse image to the covered space is quasi-coherent.  For an fpqc covering `{p i : Z i ⟶ W}` of
algebraic spaces over `X`, cartesian squares `P i j` over the pairs of members and a module `F`
on `X` with `a^*F` quasi-coherent, a family of quotients of the `aZ i ^*F` with quasi-coherent
quotient modules which agree on the `P i j` is the family of restrictions of a quotient of `a^*F`
with quasi-coherent quotient module.

This is the bijection of Stacks 08IU (surjectivity half) read over `X`: the quotients are
transported to quotients of the inverse images of `a^*F`, the squares `P i j` are compared with
the pairwise fibre products, and
`AlgebraicGeometry.Space.exists_quotientRestrict_eq_of_isFpqcCovering` descends the family.
The module is asked to be quasi-coherent on `W`, as in Stacks 08IU, where the module whose
quotients are descended is quasi-coherent. -/
@[sga "1 VIII 1.8" "partial"]
theorem descendsQuotientsAlongFpqcCovering_of_isQuasicoherentOnSite {I : Type v}
    {X W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    {P : I → I → AlgebraicSpaces B S hS} {a : W ⟶ X} {aZ : ∀ i, Z i ⟶ X}
    {aP : ∀ i j, P i j ⟶ X} (p : ∀ i, Z i ⟶ W) (r₀ : ∀ i j, P i j ⟶ Z i)
    (r₁ : ∀ i j, P i j ⟶ Z j) (hp : ∀ i, p i ≫ a = aZ i)
    (h₀ : ∀ i j, r₀ i j ≫ aZ i = aP i j) (h₁ : ∀ i j, r₁ i j ≫ aZ j = aP i j)
    (hcov : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    (hpb : ∀ i j, IsPullback (r₀ i j) (r₁ i j) (p i) (p j))
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : ((modulePullback B S hS a).obj F).IsQuasicoherentOnSite)
    (K : ∀ i, Subobject ((modulePullback B S hS (aZ i)).obj F))
    (hK : ∀ i, (cokernel (K i).arrow).IsQuasicoherentOnSite)
    (hcompat : ∀ i j, quotientRestrictOver (r₀ i j) (h₀ i j) F (K i) =
      quotientRestrictOver (r₁ i j) (h₁ i j) F (K j)) :
    ∃ K₀ : Subobject ((modulePullback B S hS a).obj F),
      (cokernel K₀.arrow).IsQuasicoherentOnSite ∧
        ∀ i, quotientRestrictOver (p i) (hp i) F K₀ = K i := by
  have hc := modulePushforwardCoherence B S hS
  obtain ⟨K₀, hK₀, hres⟩ := exists_quotientRestrict_eq_of_isFpqcCovering p hcov _ hF
    (fun i ↦ quotientTransport ((modulePullbackTriangle B S hS (hp i)).app F).symm (K i))
    (fun i ↦ isQuasicoherentOnSite_cokernel_quotientTransport _ (hK i)) fun i j ↦ by
      set Fst := QuasiCoherentDescent.pairFst B S hS Z p i j
      set Snd := QuasiCoherentDescent.pairSnd B S hS Z p i j
      have hw : Fst ≫ p i = Snd ≫ p j := QuasiCoherentDescent.pair_condition B S hS Z p i j
      set σ := (hpb i j).lift Fst Snd hw
      have hσ₀ : σ ≫ r₀ i j = Fst := (hpb i j).lift_fst _ _ _
      have hσ₁ : σ ≫ r₁ i j = Snd := (hpb i j).lift_snd _ _ _
      have hb₀ : Fst ≫ aZ i = σ ≫ aP i j := by rw [← hσ₀, Category.assoc, h₀]
      have hb₁ : Snd ≫ aZ j = σ ≫ aP i j := by rw [← hσ₁, Category.assoc, h₁]
      have hAB : quotientRestrictOver Fst hb₀ F (K i) = quotientRestrictOver Snd hb₁ F (K j) := by
        rw [← quotientRestrictOver_comp hc hσ₀ (h₀ i j) rfl hb₀,
          ← quotientRestrictOver_comp hc hσ₁ (h₁ i j) rfl hb₁, hcompat i j]
      have hkr : (Fst ≫ p i) ≫ a = σ ≫ aP i j := by rw [Category.assoc, hp i, hb₀]
      have hk' : Snd ≫ p j = Fst ≫ p i := hw.symm
      have Ei := modulePullbackTriangle_app_trans_mapIso (rfl : Fst ≫ p i = _) (hp i) hb₀ hkr F
      have Ej := modulePullbackTriangle_app_trans_mapIso hk' (hp j) hb₁ hkr F
      have hi : quotientRestrict Fst (K i) =
          quotientTransport ((modulePullbackTriangle B S hS hb₀).app F).symm
            (quotientRestrictOver Fst hb₀ F (K i)) :=
        quotientRestrict_eq_quotientTransport_quotientRestrictOver _ _ F _
      have hj : quotientRestrict Snd (K j) =
          quotientTransport ((modulePullbackTriangle B S hS hb₁).app F).symm
            (quotientRestrictOver Snd hb₁ F (K j)) :=
        quotientRestrict_eq_quotientTransport_quotientRestrictOver _ _ F _
      have e₁ : (modulePullback B S hS Fst).mapIso
            ((modulePullbackTriangle B S hS (hp i)).app F).symm ≪≫
          ((modulePullbackTriangle B S hS hb₀).app F).symm =
          ((modulePullbackTriangle B S hS hb₀).app F ≪≫ (modulePullback B S hS Fst).mapIso
            ((modulePullbackTriangle B S hS (hp i)).app F)).symm := by
        rw [Iso.trans_symm, Functor.mapIso_symm]
      have e₂ : (modulePullback B S hS Snd).mapIso
            ((modulePullbackTriangle B S hS (hp j)).app F).symm ≪≫
          ((modulePullbackTriangle B S hS hb₁).app F).symm =
          ((modulePullbackTriangle B S hS hb₁).app F ≪≫ (modulePullback B S hS Snd).mapIso
            ((modulePullbackTriangle B S hS (hp j)).app F)).symm := by
        rw [Iso.trans_symm, Functor.mapIso_symm]
      have hiso : (modulePullback B S hS Fst).mapIso
            ((modulePullbackTriangle B S hS (hp i)).app F).symm ≪≫
          ((modulePullbackTriangle B S hS hb₀).app F).symm =
          QuasiCoherentDescent.canonicalComparison Fst Snd (p i) (p j) hw
            ((modulePullback B S hS a).obj F) ≪≫
          ((modulePullback B S hS Snd).mapIso
            ((modulePullbackTriangle B S hS (hp j)).app F).symm ≪≫
          ((modulePullbackTriangle B S hS hb₁).app F).symm) := by
        rw [← modulePullbackTriangle_symm_trans_eq_canonicalComparison Fst Snd (p i) (p j) hw
          (rfl : Fst ≫ p i = _) hk' ((modulePullback B S hS a).obj F), e₁, e₂, Ei, Ej]
        apply Iso.ext
        simp only [Iso.trans_symm, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          Iso.hom_inv_id_assoc]
      rw [quotientRestrict_quotientTransport, quotientRestrict_quotientTransport, hi, hj, hAB,
        quotientTransport_trans, quotientTransport_trans, quotientTransport_trans, hiso,
        Iso.trans_assoc]
  refine ⟨K₀, hK₀, fun i ↦ ?_⟩
  rw [quotientRestrictOver_eq_quotientTransport, hres i, quotientTransport_trans,
    Iso.self_symm_id, quotientTransport_refl]

/-- **Fpqc descent of quasi-coherent quotients along a covering of an algebraic space over `X`**,
in the shape of `AlgebraicGeometry.Space.DescendsQuotientsAlongFpqcCovering`, for a module `F`
that is quasi-coherent on `X`. -/
@[sga "1 VIII 1.8" "partial"]
theorem descendsQuotientsAlongFpqcCovering_of_isQuasicoherentOnSite' {I : Type v}
    {X W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    {P : I → I → AlgebraicSpaces B S hS} {a : W ⟶ X} {aZ : ∀ i, Z i ⟶ X}
    {aP : ∀ i j, P i j ⟶ X} (p : ∀ i, Z i ⟶ W) (r₀ : ∀ i j, P i j ⟶ Z i)
    (r₁ : ∀ i j, P i j ⟶ Z j) (hp : ∀ i, p i ≫ a = aZ i)
    (h₀ : ∀ i j, r₀ i j ≫ aZ i = aP i j) (h₁ : ∀ i j, r₁ i j ≫ aZ j = aP i j)
    (hcov : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    (hpb : ∀ i j, IsPullback (r₀ i j) (r₁ i j) (p i) (p j))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (K : ∀ i, Subobject ((modulePullback B S hS (aZ i)).obj F))
    (hK : ∀ i, (cokernel (K i).arrow).IsQuasicoherentOnSite)
    (hcompat : ∀ i j, quotientRestrictOver (r₀ i j) (h₀ i j) F (K i) =
      quotientRestrictOver (r₁ i j) (h₁ i j) F (K j)) :
    ∃ K₀ : Subobject ((modulePullback B S hS a).obj F),
      (cokernel K₀.arrow).IsQuasicoherentOnSite ∧
        ∀ i, quotientRestrictOver (p i) (hp i) F K₀ = K i :=
  descendsQuotientsAlongFpqcCovering_of_isQuasicoherentOnSite p r₀ r₁ hp h₀ h₁ hcov hpb F
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a F hF) K hK hcompat

/-! ### Flatness over the base descends along an fpqc covering -/

/-- **Stacks 05VY along an fpqc covering.**  A quasi-coherent module on `W` whose inverse image
along every member of an fpqc covering `{p i : V i ⟶ W}` of algebraic spaces over `Z` is flat
over `Z` is itself flat over `Z`.

Flatness over `Z` of a quasi-coherent module is read pointwise; a point of `|W|` is the image of
a point of some `|V i|`, because an fpqc covering is jointly surjective, and there the pointwise
equivalence of Stacks 05VY for the flat morphism `p i` applies. -/
theorem flatOverDescendsAlongFpqcCovering : FlatOverDescendsAlongFpqcCovering.{u, v} B S hS := by
  intro I W Z V w v p hpv hcov M hM hflat
  have : M.IsQuasicoherentOnSite := hM
  refine (isFlatOver_iff_forall_isFlatOverAtPoint B S hS w M hM).2 fun y ↦ ?_
  obtain ⟨i, x, rfl⟩ := (isJointlySurjective_iff B S hS _ _).1
    (isJointlySurjective_of_isFpqcCovering B S hS _ hcov) y
  have hx := (isFlatOver_iff_forall_isFlatOverAtPoint B S hS (v i) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (p i) M hM)).1
      (hflat i) x
  rw [← hpv i] at hx
  exact (isFlatOverAtPoint_modulePullback_iff_of_isFlatAt B S hS (p i) w M x
    (isFlatAt_of_isFlat B S hS (p i).hom (hcov.1 i) x)).2 hx

/-! ### Finite presentation descends along an fpqc covering -/

/-- **Stacks 060V for `SheafOfModules.IsFinitePresentationOnSite`.**  A quasi-coherent module
whose inverse image along every member of an fpqc covering is of finite presentation on the site
is itself of finite presentation on the site.

The two renderings of Stacks 03DL(7) agree on the small étale site of an algebraic space
(`SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'` and
`SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation`), and for Mathlib's
`SheafOfModules.IsFinitePresentation` the descent is
`AlgebraicGeometry.Space.isFinitePresentation_of_pullback_fpqc`. -/
theorem finitePresentationOnSiteDescendsAlongFpqcCovering :
    FinitePresentationOnSiteDescendsAlongFpqcCovering.{u, v} B S hS := by
  intro I W V p hp M hM hfp
  have := isFinitePresentation_of_pullback_fpqc B S hS V p M hM hp fun i ↦
    SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _ (hfp i)
  exact SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation M

end AlgebraicGeometry.Space
