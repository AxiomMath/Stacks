module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforward
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedSumsProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveExistence
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionToposTower
public import StacksFrontier.CategoryTheory.Functor.Derived.RightDerivedComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImageComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackGood
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackAcyclic

/-!
# The derived pushforward along a composite of morphisms of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` and `g : (Sh(C'), O') ⟶ (Sh(C''), O'')` be morphisms of
ringed topoi, with sheaves of differential graded algebras `A`, `A'`, `A''` and unital
homomorphisms `φ : A' ⟶ f_*A` and `ψ : A'' ⟶ g_*A'`. This file shows that
`Rf_* ⋙ Rg_* : D(A, d) ⥤ D(A'', d)` is the right derived functor of `K(f_*) ⋙ K(g_*)`, which is
the content of [Stacks, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU).

The source deduces this from the adjunctions `Lf^* ⊣ Rf_*` and the composition of derived
pullbacks. The argument here is the same mathematics read on one side of the adjunctions: for a
good module `P` (Tag 0FSA) the base change `f^*P` corepresents `Hom(P, f_*-)`, also up to
homotopy, so homotopy classes of maps from good modules into `f_*M` are homotopy classes of maps
from good modules into `M`. Since the base change of a quasi-isomorphism of good modules is again
a quasi-isomorphism of good modules (Tag 0FSI), the direct image carries objects *local for the
quasi-isomorphisms between good modules* to such objects; K-injective modules are local for all
quasi-isomorphisms; and on morphisms out of a good module into a local object the localization
is bijective, every object being resolved by a good one (Tag 0FSH). Hence the direct image
carries a quasi-isomorphism between local objects to a quasi-isomorphism, `Rg_*` is computed by
`g_*` on local objects, and in particular on `f_*I` for `I` graded injective and K-injective.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.IsGoodLocal`: locality for the quasi-isomorphisms
  between good modules.
* `SheafOfModules.DifferentialGradedModule.BaseChangeIsGood` and
  `SheafOfModules.DifferentialGradedModule.BaseChangeIsAcyclic`: the two halves of Tag 0FSI (2)
  along a morphism of ringed topoi.

## Main results

* `SheafOfModules.DifferentialGradedModule.isGoodLocal_homotopyToposPushforward`: the direct
  image preserves good-locality.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedToposPushforwardUnit_app_of_isGoodLocal`:
  the derived pushforward is computed on good-local objects.
* `SheafOfModules.DifferentialGradedModule.isRightDerivedFunctor_derivedToposPushforward_comp`:
  `Rf_* ⋙ Rg_*` is the right derived functor of `K(f_*) ⋙ K(g_*)`.

## References

* [Stacks Project, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules.DifferentialGradedModule

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat

/-! ### Objects local for the quasi-isomorphisms between good modules -/

section Local

variable {Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}

/-- An object of the homotopy category is *good* when the module it is represents is good in the
sense of [Stacks, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA). -/
abbrev IsGoodObj (T : HomotopyCategory.{u, u, u} B) : Prop :=
  IsGoodToposBaseChange.{u, u, u} T.as

/-- An object of the homotopy category is *good-local* when it is local for the
quasi-isomorphisms between good modules. -/
abbrev IsGoodLocal (M : HomotopyCategory.{u, u, u} B) : Prop :=
  (quasiIsomorphisms.{u, u, u} B).IsLocalOn IsGoodObj M

variable (B) in
/-- **Tag 0FSH in the homotopy category**: every object receives a quasi-isomorphism from a good
module. -/
theorem exists_quasiIso_isGoodObj (T : HomotopyCategory.{u, u, u} B) :
    ∃ (P : HomotopyCategory.{u, u, u} B) (s : P ⟶ T),
      quasiIsomorphisms.{u, u, u} B s ∧ IsGoodObj P := by
  obtain ⟨P, s, hs, hP⟩ := exists_good_quasiIso.{u, u, u} (A := B) T.as
  exact ⟨(HomotopyCategory.quotient B).obj P, (HomotopyCategory.quotient B).map s,
    (quasiIsomorphisms_quotient_map_iff s).2 hs, hP⟩

variable (B) in
/-- **Tag 0FT0 in the homotopy category of a ringed topos**: K-injective modules are local for the
quasi-isomorphisms, and every object has a quasi-isomorphism into a graded injective K-injective
module. -/
theorem localResolutions_topos :
    (quasiIsomorphisms.{u, u, u} B).LocalResolutions (fun Z => IsKInjective Z.as) :=
  localResolutions.{u, u, u} (X := Y.toRingedSite) (A := B)
    (hasKInjectiveResolutions_dg.{u, u, u} (X := Y.toRingedSite) B)

/-- A K-injective module is local for all quasi-isomorphisms, and in particular good-local. -/
theorem isGoodLocal_of_isKInjective {I : DifferentialGradedModule.{u, u, u} B}
    (hI : IsKInjective I) : IsGoodLocal ((HomotopyCategory.quotient B).obj I) :=
  fun _ _ s hs _ _ => (localResolutions_topos B).bijective_comp s hs _ hI

/-- The quasi-isomorphisms of the homotopy category admit a right calculus of fractions. -/
theorem quasiIsomorphisms_hasRightCalculusOfFractions_topos :
    (quasiIsomorphisms.{u, u, u} B).HasRightCalculusOfFractions :=
  quasiIsomorphisms_hasRightCalculusOfFractions.{u, u, u} (X := Y.toRingedSite) B

/-- The quasi-isomorphisms of the homotopy category are multiplicative. -/
theorem quasiIsomorphisms_isMultiplicative_topos :
    (quasiIsomorphisms.{u, u, u} B).IsMultiplicative :=
  quasiIsomorphisms_isMultiplicative'.{u, u, u} (X := Y.toRingedSite) B

/-- **Morphisms from a good module into a good-local object** are the morphisms of the derived
category. -/
theorem bijective_toDerivedCategory_map_of_isGoodLocal {M T : HomotopyCategory.{u, u, u} B}
    (hM : IsGoodLocal M) (hT : IsGoodObj T) :
    Function.Bijective ((toDerivedCategory B).map : (T ⟶ M) → _) := by
  have := quasiIsomorphisms_hasRightCalculusOfFractions_topos (B := B)
  have := quasiIsomorphisms_isMultiplicative_topos (B := B)
  exact Localization.bijective_map_of_isLocalOn (toDerivedCategory B)
    (quasiIsomorphisms.{u, u, u} B) IsGoodObj (exists_quasiIso_isGoodObj B) hM hT

/-- Postcomposition with a quasi-isomorphism of good-local objects is bijective on morphisms out
of a good module. -/
theorem bijective_comp_of_isGoodLocal {M M' T : HomotopyCategory.{u, u, u} B}
    (hM : IsGoodLocal M) (hM' : IsGoodLocal M') (s : M ⟶ M')
    (hs : quasiIsomorphisms.{u, u, u} B s) (hT : IsGoodObj T) :
    Function.Bijective (fun a : T ⟶ M => a ≫ s) := by
  have := quasiIsomorphisms_hasRightCalculusOfFractions_topos (B := B)
  have := quasiIsomorphisms_isMultiplicative_topos (B := B)
  exact Localization.bijective_comp_map_of_isLocalOn (toDerivedCategory B)
    (quasiIsomorphisms.{u, u, u} B) IsGoodObj (exists_quasiIso_isGoodObj B) hM hM' s hs hT

end Local

/-! ### Good-locality is carried along the direct image -/

section Transfer

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hφ : φ.IsUnital)

/-- Every object corepresenting the base change of a good module along `(f, A, φ)` is good: the
goodness half of [Stacks, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI) (2). -/
def BaseChangeIsGood : Prop :=
  ∀ (P : DifferentialGradedModule.{u, u, u} B), IsGoodToposBaseChange.{u, u, u} P →
    ∀ (T : DifferentialGradedModule.{u, u, u} A),
      (toposPushforward (toposDirectImageModules f) φ hφ ⋙
        coyoneda.obj (Opposite.op P)).CorepresentableBy T →
      IsGoodToposBaseChange.{u, u, u} T

/-- Every object corepresenting the base change of a good acyclic module along `(f, A, φ)` is
acyclic: the acyclicity half of [Stacks, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
(2). -/
def BaseChangeIsAcyclic : Prop :=
  ∀ (P : DifferentialGradedModule.{u, u, u} B), IsGoodToposBaseChange.{u, u, u} P →
    P.complex.Acyclic →
    ∀ (T : DifferentialGradedModule.{u, u, u} A),
      (toposPushforward (toposDirectImageModules f) φ hφ ⋙
        coyoneda.obj (Opposite.op P)).CorepresentableBy T →
      T.complex.Acyclic

/-- **The goodness half of Tag 0FSI (2) along `(f, A, φ)`**: every base change of a good module
is good. This is `SheafOfModules.isGoodToposBaseChange_of_toposCorepresentableBy`. -/
theorem baseChangeIsGood : BaseChangeIsGood f φ hφ :=
  fun _ hP _ e => isGoodToposBaseChange_of_toposCorepresentableBy f φ hφ hP e

/-- **The acyclicity half of Tag 0FSI (2) along `(f, A, φ)`**: every base change of a good
acyclic module is acyclic. This is
`acyclic_of_toposCorepresentableBy_of_isGoodToposBaseChange`. -/
theorem baseChangeIsAcyclic : BaseChangeIsAcyclic f φ hφ :=
  fun _ hP hac _ e => acyclic_of_toposCorepresentableBy_of_isGoodToposBaseChange f φ hφ hP hac e

/-- A map conjugate to a bijection by two equivalences is bijective. -/
private theorem bijective_of_comp_equiv {α β γ δ : Sort*} {f : β → δ} {g : α → γ}
    (E : α ≃ β) (E' : γ ≃ δ) (hg : Function.Bijective g) (h : ∀ a, f (E a) = E' (g a)) :
    Function.Bijective f := by
  have : f = E' ∘ g ∘ E.symm := funext fun b => by simpa using h (E.symm b)
  exact this ▸ E'.bijective.comp (hg.comp E.symm.bijective)

variable {f φ hφ}

/-- The transpose through two base changes is compatible with precomposition, read on homotopy
classes: precomposing with the class of `s` on the side of the direct image is precomposing
with the class of the base change of `s` on the side of the base change. -/
theorem homotopyHomEquiv_baseChangeHom_comp {P P' : DifferentialGradedModule.{u, u, u} B}
    {T T' : DifferentialGradedModule.{u, u, u} A}
    (e : (toposPushforward (toposDirectImageModules f) φ hφ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward (toposDirectImageModules f) φ hφ ⋙
      coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (s : P ⟶ P') {Q : DifferentialGradedModule.{u, u, u} A}
    (a : (HomotopyCategory.quotient A).obj T' ⟶ (HomotopyCategory.quotient A).obj Q) :
    homotopyHomEquiv (toposDirectImageModules f) φ hφ e Q
        ((HomotopyCategory.quotient A).map
          (baseChangeHom (toposDirectImageModules f) φ hφ e e' s) ≫ a) =
      (HomotopyCategory.quotient B).map s ≫
        homotopyHomEquiv (toposDirectImageModules f) φ hφ e' Q a := by
  obtain ⟨k, rfl⟩ := (HomotopyCategory.quotient A).map_surjective a
  rw [← Functor.map_comp, homotopyHomEquiv_map, homotopyHomEquiv_map,
    homEquiv_baseChangeHom_comp, Functor.map_comp]
  rfl

/-- **The base change of a quasi-isomorphism of good modules is a quasi-isomorphism of good
modules**: its cone corepresents the base change of the cone, which is good and acyclic. -/
theorem quasiIso_baseChangeHom (hacyc : BaseChangeIsAcyclic f φ hφ)
    {P P' : DifferentialGradedModule.{u, u, u} B}
    {T T' : DifferentialGradedModule.{u, u, u} A}
    (e : (toposPushforward (toposDirectImageModules f) φ hφ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward (toposDirectImageModules f) φ hφ ⋙
      coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (s : P ⟶ P') (hs : QuasiIso s.toHomologicalComplex)
    (hP : IsGoodToposBaseChange.{u, u, u} P) (hP' : IsGoodToposBaseChange.{u, u, u} P') :
    QuasiIso (baseChangeHom (toposDirectImageModules f) φ hφ e e' s).toHomologicalComplex :=
  (acyclic_cone_iff_quasiIso A (baseChangeHom (toposDirectImageModules f) φ hφ e e' s)).1
    (hacyc (cone s) (cone_isGoodToposBaseChange s hP hP') ((acyclic_cone_iff_quasiIso B s).2 hs)
      _ (coneToposCorepresentableBy (toposDirectImageModules f) φ hφ e e' s))

/-- **Good-locality is carried along the direct image.** If `M` is local for the
quasi-isomorphisms between good `A`-modules, then `f_*M` is local for the quasi-isomorphisms
between good `B`-modules: through the base change of good modules, precomposition with a
quasi-isomorphism of good `B`-modules is precomposition with its base change, a
quasi-isomorphism of good `A`-modules. -/
theorem isGoodLocal_homotopyToposPushforward (hgood : BaseChangeIsGood f φ hφ)
    (hacyc : BaseChangeIsAcyclic f φ hφ) {M : HomotopyCategory.{u, u, u} A}
    (hM : IsGoodLocal M) :
    IsGoodLocal ((homotopyToposPushforward (toposDirectImageModules f) φ hφ).obj M) := by
  intro K L s hs hK hL
  obtain ⟨s₀, rfl⟩ := (HomotopyCategory.quotient B).map_surjective s
  have hs₀ : QuasiIso s₀.toHomologicalComplex := (quasiIsomorphisms_quotient_map_iff s₀).1 hs
  obtain ⟨T, ⟨e⟩⟩ := (hK.baseChange f A φ hφ).1
  obtain ⟨T', ⟨e'⟩⟩ := (hL.baseChange f A φ hφ).1
  have ht := quasiIso_baseChangeHom hacyc e e' s₀ hs₀ hK hL
  have hb := hM (Y := (HomotopyCategory.quotient A).obj T)
    (X := (HomotopyCategory.quotient A).obj T')
    ((HomotopyCategory.quotient A).map (baseChangeHom (toposDirectImageModules f) φ hφ e e' s₀))
    ((quasiIsomorphisms_quotient_map_iff _).2 ht) (hgood _ hK T e) (hgood _ hL T' e')
  exact bijective_of_comp_equiv (homotopyHomEquiv (toposDirectImageModules f) φ hφ e' M.as)
    (homotopyHomEquiv (toposDirectImageModules f) φ hφ e M.as)
    hb fun a => (homotopyHomEquiv_baseChangeHom_comp e e' s₀ a).symm

end Transfer

/-! ### The derived pushforward is computed on good-local objects -/

section Computed

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y}
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  {φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A} {hφ : φ.IsUnital}

/-- The direct image carries a quasi-isomorphism of good-local objects to a morphism which
becomes invertible in the derived category: on morphisms out of a good module it is, through the
base change, postcomposition with the quasi-isomorphism, and both ends stay good-local. -/
theorem isIso_toDerivedCategory_map_homotopyToposPushforward_map
    (hgood : BaseChangeIsGood f φ hφ) (hacyc : BaseChangeIsAcyclic f φ hφ)
    {M N : HomotopyCategory.{u, u, u} A} (hM : IsGoodLocal M) (hN : IsGoodLocal N)
    (s : M ⟶ N) (hs : quasiIsomorphisms.{u, u, u} A s) :
    IsIso ((toDerivedCategory B).map
      ((homotopyToposPushforward (toposDirectImageModules f) φ hφ).map s)) := by
  have := quasiIsomorphisms_hasRightCalculusOfFractions_topos (B := B)
  have := quasiIsomorphisms_isMultiplicative_topos (B := B)
  refine Localization.isIso_map_of_bijective_comp (toDerivedCategory B)
    (quasiIsomorphisms.{u, u, u} B) IsGoodObj (exists_quasiIso_isGoodObj B)
    (isGoodLocal_homotopyToposPushforward hgood hacyc hM)
    (isGoodLocal_homotopyToposPushforward hgood hacyc hN) _ fun P hP => ?_
  obtain ⟨T, ⟨e⟩⟩ := (hP.baseChange f A φ hφ).1
  have hb := bijective_comp_of_isGoodLocal hM hN s hs (hgood _ hP T e)
  exact bijective_of_comp_equiv (homotopyHomEquiv (toposDirectImageModules f) φ hφ e M.as)
    (homotopyHomEquiv (toposDirectImageModules f) φ hφ e N.as) hb fun a =>
    by rw [homotopyHomEquiv_comp]

/-- **The derived pushforward is computed on good-local objects**: its comparison map is
invertible at every object local for the quasi-isomorphisms between good modules. Resolve the
object by a graded injective K-injective module; the comparison map is invertible there, and the
direct image of the resolving quasi-isomorphism becomes invertible in the derived category. -/
theorem isIso_derivedToposPushforwardUnit_app_of_isGoodLocal
    (hgood : BaseChangeIsGood f φ hφ) (hacyc : BaseChangeIsAcyclic f φ hφ)
    {M : HomotopyCategory.{u, u, u} A} (hM : IsGoodLocal M) :
    IsIso ((derivedToposPushforwardUnit f A B φ hφ).app M) := by
  obtain ⟨I, s₀, hs₀, hGI, hKI⟩ :=
    hasKInjectiveResolutions_dg.{u, u, u} (X := X.toRingedSite) A M.as
  let s : M ⟶ (HomotopyCategory.quotient A).obj I := (HomotopyCategory.quotient A).map s₀
  have hs : quasiIsomorphisms.{u, u, u} A s := (quasiIsomorphisms_quotient_map_iff s₀).2 hs₀
  have h₁ : IsIso ((derivedToposPushforwardUnit f A B φ hφ).app
      ((HomotopyCategory.quotient A).obj I)) :=
    isIso_derivedToposPushforwardUnit_app f A B φ hφ ⟨hGI, hKI⟩
  have h₂ : IsIso ((toposPushforwardToDerived f A B φ hφ).map s) :=
    isIso_toDerivedCategory_map_homotopyToposPushforward_map hgood hacyc hM
      (isGoodLocal_of_isKInjective hKI) s hs
  have h₃ : IsIso ((toDerivedCategory A ⋙ derivedToposPushforward f A B φ hφ).map s) := by
    have : IsIso ((toDerivedCategory A).map s) :=
      Localization.inverts (toDerivedCategory A) (quasiIsomorphisms.{u, u, u} A) s hs
    exact inferInstanceAs (IsIso ((derivedToposPushforward f A B φ hφ).map
      ((toDerivedCategory A).map s)))
  have : IsIso ((derivedToposPushforwardUnit f A B φ hφ).app M ≫
      (toDerivedCategory A ⋙ derivedToposPushforward f A B φ hφ).map s) := by
    rw [← (derivedToposPushforwardUnit f A B φ hφ).naturality s]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((toDerivedCategory A ⋙ derivedToposPushforward f A B φ hφ).map s)

end Computed

/-! ### The composite of two derived pushforwards -/

section Composite

variable {X : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

variable (X) in
/-- **Tag 0FT0 in the homotopy category of a ringed topos**: every object has a quasi-isomorphism
into a graded injective K-injective module. -/
theorem exists_quasiIso_isDGInjective_topos
    (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (K : HomotopyCategory.{u, u, u} A) :
    ∃ (I : HomotopyCategory.{u, u, u} A) (s : K ⟶ I),
      quasiIsomorphisms.{u, u, u} A s ∧ (IsKInjective I.as ∧ GradedInjective I.as) :=
  exists_quasiIso_isDGInjective.{u, u, u} (X := X.toRingedSite) A K

/-- **Tag 0FT8 in the homotopy category of a ringed topos**: the localization is bijective on
morphisms into a K-injective module. -/
theorem bijective_toDerivedCategory_map_topos
    {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
    (I : HomotopyCategory.{u, u, u} A) (hI : IsKInjective I.as ∧ GradedInjective I.as)
    (K : HomotopyCategory.{u, u, u} A) :
    Function.Bijective ((toDerivedCategory A).map : (K ⟶ I) → _) :=
  bijective_toDerivedCategory_map_of_isKInjective.{u, u, u} (X := X.toRingedSite) (A := A)
    (hasKInjectiveResolutions_dg.{u, u, u} (X := X.toRingedSite) A) K hI.1

variable {Y Z : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y}
  {g : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z}
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  {C : DifferentialGradedAlgebra.{u, u} (toRingCat Z.J Z.O)}
  {φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A} {hφ : φ.IsUnital}
  {ψ : C ⟶ toposPushforwardAlgebra (toposDirectImageModules g) B} {hψ : ψ.IsUnital}

/-- **`Rf_* ⋙ Rg_*` is the right derived functor of `K(f_*) ⋙ K(g_*)`**, with the composite of
the two comparison maps. At a graded injective K-injective `A`-module `I` the comparison map of
`Rf_*` is invertible, and `f_*I` is local for the quasi-isomorphisms between good modules, so the
comparison map of `Rg_*` is invertible at `f_*I`. -/
theorem isRightDerivedFunctor_derivedToposPushforward_comp
    (hgood : BaseChangeIsGood g ψ hψ) (hacyc : BaseChangeIsAcyclic g ψ hψ)
    (hgood' : BaseChangeIsGood f φ hφ) (hacyc' : BaseChangeIsAcyclic f φ hφ) :
    (derivedToposPushforward f A B φ hφ ⋙ derivedToposPushforward g B C ψ hψ).IsRightDerivedFunctor
      (Functor.rightDerivedCompUnit (derivedToposPushforwardUnit f A B φ hφ)
        (derivedToposPushforwardUnit g B C ψ hψ)) (quasiIsomorphisms.{u, u, u} A) :=
  Functor.isRightDerivedFunctor_comp_of_isIso (quasiIsomorphisms.{u, u, u} A) _ _
    (fun I => IsKInjective I.as ∧ GradedInjective I.as) (exists_quasiIso_isDGInjective_topos X A)
    bijective_toDerivedCategory_map_topos
    (fun _ hI => isIso_derivedToposPushforwardUnit_app f A B φ hφ ⟨hI.2, hI.1⟩)
    (fun _ hI => isIso_derivedToposPushforwardUnit_app_of_isGoodLocal hgood hacyc
      (isGoodLocal_homotopyToposPushforward hgood' hacyc' (isGoodLocal_of_isKInjective hI.1)))

end Composite

/-! ### Derived pushforward along a third morphism playing the composite -/

section Assembly

variable {X Y Z : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y}
  {g : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z}
  {h : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z}
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  {C : DifferentialGradedAlgebra.{u, u} (toRingCat Z.J Z.O)}
  {φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A} {hφ : φ.IsUnital}
  {ψ : C ⟶ toposPushforwardAlgebra (toposDirectImageModules g) B} {hψ : ψ.IsUnital}
  {χ : C ⟶ toposPushforwardAlgebra (toposDirectImageModules h) A} {hχ : χ.IsUnital}

/-- The comparison of the direct images on homotopy categories induced by a comparison of the
direct images of differential graded modules. -/
noncomputable def homotopyToposPushforwardCompIso
    (e : toposPushforward (toposDirectImageModules h) χ hχ ≅
      toposPushforward (toposDirectImageModules f) φ hφ ⋙
        toposPushforward (toposDirectImageModules g) ψ hψ) :
    homotopyToposPushforward (toposDirectImageModules h) χ hχ ≅
      homotopyToposPushforward (toposDirectImageModules f) φ hφ ⋙
        homotopyToposPushforward (toposDirectImageModules g) ψ hψ :=
  HomotopyCategory.descendNatIso _ (PreservesHomotopic.comp
      (preservesHomotopic_toposPushforward _ φ hφ)
      (preservesHomotopic_toposPushforward _ ψ hψ)) e ≪≫
    eqToIso (HomotopyCategory.descend_comp _ _ _ _)

/-- An isomorphism `R h_* ≅ Rf_* ⋙ Rg_*` is *induced by* an isomorphism `e` of direct images when,
composed with the comparison map of `R h_*`, it is the image of `e` on homotopy categories
followed by the composite of the comparison maps of `Rf_*` and `Rg_*`. -/
def IsInducedDerivedCompIso
    (e : toposPushforward (toposDirectImageModules h) χ hχ ≅
      toposPushforward (toposDirectImageModules f) φ hφ ⋙
        toposPushforward (toposDirectImageModules g) ψ hψ)
    (η : derivedToposPushforward h A C χ hχ ≅
      derivedToposPushforward f A B φ hφ ⋙ derivedToposPushforward g B C ψ hψ) : Prop :=
  derivedToposPushforwardUnit h A C χ hχ ≫ Functor.whiskerLeft (toDerivedCategory A) η.hom =
    Functor.whiskerRight (homotopyToposPushforwardCompIso e).hom (toDerivedCategory C) ≫
      Functor.rightDerivedCompUnit (derivedToposPushforwardUnit f A B φ hφ)
        (derivedToposPushforwardUnit g B C ψ hψ)

/-- **The derived pushforward along `h` is the derived pushforward along `f` followed by the
derived pushforward along `g`**, for any morphism `h` whose direct image of differential graded
modules is identified with the composite of those of `f` and `g`. Both are right derived functors
of the direct image along `h` followed by the localization. -/
noncomputable def derivedToposPushforwardCompIso
    (hgood : BaseChangeIsGood g ψ hψ) (hacyc : BaseChangeIsAcyclic g ψ hψ)
    (hgood' : BaseChangeIsGood f φ hφ) (hacyc' : BaseChangeIsAcyclic f φ hφ)
    (e : toposPushforward (toposDirectImageModules h) χ hχ ≅
      toposPushforward (toposDirectImageModules f) φ hφ ⋙
        toposPushforward (toposDirectImageModules g) ψ hψ) :
    derivedToposPushforward h A C χ hχ ≅
      derivedToposPushforward f A B φ hφ ⋙ derivedToposPushforward g B C ψ hψ :=
  have := isRightDerivedFunctor_derivedToposPushforward_comp hgood hacyc hgood' hacyc'
  Functor.rightDerivedNatIso _ _ (derivedToposPushforwardUnit h A C χ hχ)
    (Functor.rightDerivedCompUnit (derivedToposPushforwardUnit f A B φ hφ)
      (derivedToposPushforwardUnit g B C ψ hψ)) (quasiIsomorphisms.{u, u, u} A)
    (Functor.isoWhiskerRight (homotopyToposPushforwardCompIso e) (toDerivedCategory C))

/-- The comparison of derived pushforwards is compatible with the comparison of the direct images
on homotopy categories and with the comparison maps of the three derived pushforwards: it is the
unique such comparison. -/
theorem derivedToposPushforwardCompIso_fac
    (hgood : BaseChangeIsGood g ψ hψ) (hacyc : BaseChangeIsAcyclic g ψ hψ)
    (hgood' : BaseChangeIsGood f φ hφ) (hacyc' : BaseChangeIsAcyclic f φ hφ)
    (e : toposPushforward (toposDirectImageModules h) χ hχ ≅
      toposPushforward (toposDirectImageModules f) φ hφ ⋙
        toposPushforward (toposDirectImageModules g) ψ hψ) :
    derivedToposPushforwardUnit h A C χ hχ ≫
        Functor.whiskerLeft (toDerivedCategory A)
          (derivedToposPushforwardCompIso hgood hacyc hgood' hacyc' e).hom =
      Functor.whiskerRight (homotopyToposPushforwardCompIso e).hom (toDerivedCategory C) ≫
        Functor.rightDerivedCompUnit (derivedToposPushforwardUnit f A B φ hφ)
          (derivedToposPushforwardUnit g B C ψ hψ) := by
  have := isRightDerivedFunctor_derivedToposPushforward_comp hgood hacyc hgood' hacyc'
  rw [derivedToposPushforwardCompIso, Functor.rightDerivedNatIso_hom]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _ (quasiIsomorphisms.{u, u, u} A) _

end Assembly

/-! ### The composite, given the two halves of Tag 0FSI (2) -/

section OfBaseChange

variable {X Y Z : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **The derived pushforward along a morphism playing the composite.** Let `f : X ⟶ Y`,
`g : Y ⟶ Z` and `h : X ⟶ Z` be morphisms of ringed topoi whose geometric direct images are
related by `τ : f_* ⋙ g_* ≅ h_*`, compatibly with the structure maps, so that `h` is `g ∘ f`
up to `τ`. For sheaves of differential graded algebras `A`, `B`, `C` on `X`, `Y`, `Z` and unital
homomorphisms `φ : B ⟶ f_*A` and `ψ : C ⟶ g_*B`, the derived pushforward along `h` and the
composite homomorphism `C ⟶ g_*B ⟶ g_*f_*A ≅ h_*A` is the derived pushforward along `f`
followed by the derived pushforward along `g`, by an isomorphism compatible with the comparison of
direct images and with the comparison maps of the three derived pushforwards. -/
theorem exists_derivedToposPushforwardCompIso_of_baseChange
    (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (g : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
    (h : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
    (τ : f.toToposHom.pushforward ⋙ g.toToposHom.pushforward ≅ h.toToposHom.pushforward)
    (compat : fSharpSetComp f g ≫
        τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      fSharpSet h)
    (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O))
    (C : DifferentialGradedAlgebra.{u, u} (toRingCat Z.J Z.O))
    (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (unitalφ : φ.IsUnital)
    (ψ : C ⟶ toposPushforwardAlgebra (toposDirectImageModules g) B) (unitalψ : ψ.IsUnital)
    (hgood : BaseChangeIsGood g ψ unitalψ) (hacyc : BaseChangeIsAcyclic g ψ unitalψ)
    (hgood' : BaseChangeIsGood f φ unitalφ) (hacyc' : BaseChangeIsAcyclic f φ unitalφ) :
    ∃ e : derivedToposPushforward h A C (toposPushforwardCompAlgebraHom f g h τ compat A φ ψ)
          (isUnital_toposPushforwardCompAlgebraHom f g h τ compat A φ ψ unitalφ unitalψ) ≅
        derivedToposPushforward f A B φ unitalφ ⋙ derivedToposPushforward g B C ψ unitalψ,
      derivedToposPushforwardUnit h A C _ _ ≫ Functor.whiskerLeft (toDerivedCategory A) e.hom =
        Functor.whiskerRight (homotopyToposPushforwardCompIso
            (toposPushforwardCompIsoOfComparison f g h τ compat A unitalφ unitalψ)).hom
            (toDerivedCategory C) ≫
          Functor.rightDerivedCompUnit (derivedToposPushforwardUnit f A B φ unitalφ)
            (derivedToposPushforwardUnit g B C ψ unitalψ) :=
  ⟨derivedToposPushforwardCompIso hgood hacyc hgood' hacyc'
      (toposPushforwardCompIsoOfComparison f g h τ compat A unitalφ unitalψ),
    derivedToposPushforwardCompIso_fac _ _ _ _ _⟩

/-- The composite along the literal composite `g ∘ f` of two morphisms of ringed topoi, given the
two halves of Tag 0FSI (2) along `f` and along `g`. -/
theorem exists_derivedToposPushforwardCompIso_comp_of_baseChange
    (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)
    (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O))
    (C : DifferentialGradedAlgebra.{u, u} (toRingCat Z.J Z.O))
    (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f.toModulesHom) A)
    (unitalφ : φ.IsUnital)
    (ψ : C ⟶ toposPushforwardAlgebra (toposDirectImageModules g.toModulesHom) B)
    (unitalψ : ψ.IsUnital)
    (hgood : BaseChangeIsGood g.toModulesHom ψ unitalψ)
    (hacyc : BaseChangeIsAcyclic g.toModulesHom ψ unitalψ)
    (hgood' : BaseChangeIsGood f.toModulesHom φ unitalφ)
    (hacyc' : BaseChangeIsAcyclic f.toModulesHom φ unitalφ) :
    ∃ e : derivedToposPushforward (g.comp f).toModulesHom A C (toposCompAlgebraHom f g A φ ψ)
          (isUnital_toposCompAlgebraHom f g A unitalφ unitalψ) ≅
        derivedToposPushforward f.toModulesHom A B φ unitalφ ⋙
          derivedToposPushforward g.toModulesHom B C ψ unitalψ,
      derivedToposPushforwardUnit _ A C _ _ ≫ Functor.whiskerLeft (toDerivedCategory A) e.hom =
        Functor.whiskerRight (homotopyToposPushforwardCompIso
            (toposPushforwardRingedCompIso f g A unitalφ unitalψ)).hom (toDerivedCategory C) ≫
          Functor.rightDerivedCompUnit (derivedToposPushforwardUnit f.toModulesHom A B φ unitalφ)
            (derivedToposPushforwardUnit g.toModulesHom B C ψ unitalψ) :=
  ⟨derivedToposPushforwardCompIso hgood hacyc hgood' hacyc'
      (toposPushforwardRingedCompIso f g A unitalφ unitalψ),
    derivedToposPushforwardCompIso_fac _ _ _ _ _⟩

end OfBaseChange


/-! ### The composite along the composite morphism of ringed topoi -/

section Literal

variable {X Y Z : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **`R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*`**, with the compatibility of `forget₂ CommRingCat RingCat` with
sheaves as instance arguments. The statement of
[Stacks, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU) itself, in which that compatibility
is discharged, is `SheafOfModules.DifferentialGradedModule.derivedToposPushforward_comp`. -/
theorem exists_derivedToposPushforwardCompIso_comp
    (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)
    (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O))
    (C : DifferentialGradedAlgebra.{u, u} (toRingCat Z.J Z.O))
    (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f.toModulesHom) A)
    (unitalφ : φ.IsUnital)
    (ψ : C ⟶ toposPushforwardAlgebra (toposDirectImageModules g.toModulesHom) B)
    (unitalψ : ψ.IsUnital) :
    ∃ (ηU : toposPushforward (toposDirectImageModules (g.comp f).toModulesHom)
          (toposCompAlgebraHom f g A φ ψ) (isUnital_toposCompAlgebraHom f g A unitalφ unitalψ) ≅
        toposPushforward (toposDirectImageModules f.toModulesHom) φ unitalφ ⋙
          toposPushforward (toposDirectImageModules g.toModulesHom) ψ unitalψ)
      (ηD : derivedToposPushforward (g.comp f).toModulesHom A C (toposCompAlgebraHom f g A φ ψ)
          (isUnital_toposCompAlgebraHom f g A unitalφ unitalψ) ≅
        derivedToposPushforward f.toModulesHom A B φ unitalφ ⋙
          derivedToposPushforward g.toModulesHom B C ψ unitalψ),
      (∀ (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ),
        (ηU.inv.app M).toHomologicalComplex.f n =
          (toposDirectImageModulesCompIso f g).hom.app (M.complex.X n)) ∧
      IsInducedDerivedCompIso ηU ηD :=
  ⟨toposPushforwardRingedCompIso f g A unitalφ unitalψ,
    derivedToposPushforwardCompIso (baseChangeIsGood _ _ _) (baseChangeIsAcyclic _ _ _)
      (baseChangeIsGood _ _ _) (baseChangeIsAcyclic _ _ _)
      (toposPushforwardRingedCompIso f g A unitalφ unitalψ),
    toposPushforwardRingedCompIso_inv_app_f f g A unitalφ unitalψ,
    derivedToposPushforwardCompIso_fac _ _ _ _ _⟩

end Literal



/-! ### Tag 0FTU -/

section Tag

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

variable {X Y Z : AlgebraicGeometry.RingedTopos.{u, u, u}}

/-- **Stacks Tag 0FTU.** Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(C'), O')` and
`(g, g♯) : (Sh(C'), O') ⟶ (Sh(C''), O'')` be morphisms of ringed topoi. Let `A`, `A'` and `A''`
be a differential graded `O`-algebra, `O'`-algebra and `O''`-algebra, and let `φ : A' ⟶ f_*A`
and `φ' : A'' ⟶ g_*A'` be homomorphisms of differential graded algebras. Then
`R(g ∘ f)_* = Rg_* ∘ Rf_* : D(A, d) ⟶ D(A'', d)`.

Here `R(g ∘ f)_*` is the derived pushforward along the composite morphism of ringed topoi
`g.comp f` and the composite homomorphism `A'' ⟶ g_*A' ⟶ g_*f_*A = (g ∘ f)_*A`
(`toposCompAlgebraHom`, degreewise `toposCompAlgebraHom_f`), and each derived pushforward is the
right derived extension of the direct image of differential graded modules on homotopy
categories (`derivedToposPushforward`). The three clauses are:

1. the direct image of differential graded modules along `g ∘ f` is the direct image along `f`
   followed by the direct image along `g`, by the isomorphism `ηU` which in every degree is the
   comparison `(g ∘ f)_* ≅ g_* ∘ f_*` of direct images of sheaves of modules;
2. `R(g ∘ f)_*` is isomorphic to `Rf_*` followed by `Rg_*`, by an isomorphism `ηD`;
3. `ηD` is the one induced by `ηU` (`IsInducedDerivedCompIso`): composed with the comparison map
   of `R(g ∘ f)_*` it is the image of `ηU` followed by the composite of the comparison maps of
   `Rf_*` and `Rg_*`.

The equality of the source is an isomorphism here, the derived functors being pinned by their
universal property. The ringed topoi have their sites and structure sheaves in one universe, the
setting of the K-injective resolutions of Tag 0FT0. -/
@[stacks 0FTU]
theorem derivedToposPushforward_comp
    (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)
    (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (A' : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O))
    (A'' : DifferentialGradedAlgebra.{u, u} (toRingCat Z.J Z.O))
    (φ : A' ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
      (toposDirectImageModules (X := X) (Y := Y) f.toModulesHom) A)
    (unitalφ : φ.IsUnital)
    (φ' : A'' ⟶ toposPushforwardAlgebra (Osharp := Y.O) (Psharp := Z.O)
      (toposDirectImageModules (X := Y) (Y := Z) g.toModulesHom) A')
    (unitalφ' : φ'.IsUnital) :
    ∃ (ηU : toposPushforward (toposDirectImageModules (X := X) (Y := Z) (g.comp f).toModulesHom)
          (toposCompAlgebraHom (X := X) (Y := Y) (Z := Z) f g A φ φ')
          (isUnital_toposCompAlgebraHom (X := X) (Y := Y) (Z := Z) f g A unitalφ unitalφ') ≅
        toposPushforward (toposDirectImageModules (X := X) (Y := Y) f.toModulesHom) φ unitalφ ⋙
          toposPushforward (toposDirectImageModules (X := Y) (Y := Z) g.toModulesHom) φ' unitalφ')
      (ηD : derivedToposPushforward (X := X) (Y := Z) (g.comp f).toModulesHom A A''
          (toposCompAlgebraHom (X := X) (Y := Y) (Z := Z) f g A φ φ')
          (isUnital_toposCompAlgebraHom (X := X) (Y := Y) (Z := Z) f g A unitalφ unitalφ') ≅
        derivedToposPushforward (X := X) (Y := Y) f.toModulesHom A A' φ unitalφ ⋙
          derivedToposPushforward (X := Y) (Y := Z) g.toModulesHom A' A'' φ' unitalφ'),
      (∀ (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ),
        (ηU.inv.app M).toHomologicalComplex.f n =
          (toposDirectImageModulesCompIso (X := X) (Y := Y) (Z := Z) f g).hom.app
            (M.complex.X n)) ∧
      IsInducedDerivedCompIso ηU ηD :=
  exists_derivedToposPushforwardCompIso_comp f g A A' A'' φ unitalφ φ' unitalφ'

end Tag

end SheafOfModules.DifferentialGradedModule
