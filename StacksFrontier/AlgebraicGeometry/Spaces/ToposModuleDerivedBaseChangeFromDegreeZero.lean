module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeMap
public import StacksFrontier.Homology.DerivedCategory.RightDerivedInjectiveModel
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria

/-!
# The base change map of Stacks 0736 in `D⁺` is invertible as soon as its degree-zero case is

Let

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

be a commutative square of algebraic spaces over a scheme `S`.  **Stacks 0736** has a degree-zero
base change map `g^*f_* ⟶ f'_*(g')^*`, which this development writes
`AlgebraicGeometry.Space.toposModuleBaseChangeMap`, and a derived one
`g^*Rf_* ⟶ Rf'_*(g')^*` on `D⁺`, which it writes
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap`; the second is
`Stacks.Cohomology.BaseChange.derived` of the first.

This file proves that **the derived one is invertible at every object of `D⁺(𝒪_X)` as soon as the
degree-zero one is invertible and `(g')^*` carries injective `𝒪_X`-modules to injective
`𝒪_{X'}`-modules.**  It is, as far as the author could measure, the first declaration in this
development that asserts invertibility of `toposModuleDerivedBaseChangeMap` — equivalently of
`Stacks.Cohomology.ToposBaseChange.baseChangeMap`, which it is by
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap_eq_baseChangeMap` — under any
hypotheses at all.

*That claim is about three names and not about the mathematics.*  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleDerivedBaseChangeChartwise.lean` say that
nothing
in the development asserts invertibility of `toposModuleDerivedBaseChangeMap`, of
`Stacks.Cohomology.ToposBaseChange.baseChangeMap` or of
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeMap` under any hypothesis.  That is true of
those three names and would be misleading read as a statement about **Stacks 073K**, part (1):  the
degree-zero clause of part (1) **is** proved, with no affineness, as
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFlatBaseChangeQuasicoherent.lean`) — for a cartesian
square with `g` flat and `f` quasi-compact and quasi-separated, at every quasi-coherent
coefficient.  It is a statement about `AlgebraicGeometry.Space.moduleBaseChangeMap`, the other
spelling of the degree-zero map, and it does not discharge the hypothesis below:  not only is the
crossing of the two spellings missing (second implementation note), but the hypothesis below is
invertibility at *injective* coefficients, and an injective `𝒪_X`-module is not quasi-coherent.

## Main results

* `isIso_toposModuleDerivedBaseChangeMap_app_of_isIso_toposModuleBaseChangeMap_app_injective`:
  **the derived base change map of Stacks 0736 is invertible at every `M` of `D⁺(𝒪_X)` when the
  degree-zero base change map of the square is invertible at every injective coefficient and
  `(g')^*` preserves injective objects.**  Injectivity of the coefficient is the only place the
  degree-zero hypothesis is used.
* `isIso_toposModuleDerivedBaseChangeMap_app_of_isIso_toposModuleBaseChangeMap`:
  the same with the degree-zero hypothesis read at every coefficient.
* `AlgebraicGeometry.Space.preservesInjectiveObjects_modulePullback_of_isEtale`: the inverse image
  of `𝒪`-modules along an étale morphism of algebraic spaces preserves injective objects —
  **Stacks 03F3**, part (1), transported from the étale-restriction spelling to
  `AlgebraicGeometry.Space.modulePullback` along **Stacks 03LW**.
* `AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale_source`: for a
  square whose *source* leg `g'` is étale, the derived base change map is invertible at every `M`
  as soon as the degree-zero base change map is invertible.  For a cartesian square with `g`
  étale, `g'` is étale too and the degree-zero map is invertible, so the étale case follows
  unconditionally;  it is
  `AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale`.

## Implementation notes

*What the proof is.*  Leray's acyclicity lemma and nothing else.  An object `M` of `D⁺(𝒪_X)` is
isomorphic to the image of a bounded below cochain complex `K` of injective `𝒪_X`-modules
(`CategoryTheory.DerivedCategory.Plus.exists_injective_nonempty_iso`, used at the bound `M` carries
in its second component), and invertibility of a component of a natural transformation transfers
along an isomorphism of the object.  At `K` the criterion
`Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_of_acyclic` applies:  its four hypotheses are

* the unit of `Rf_*` at `K` — invertible because the terms of `K` are injective, hence right
  acyclic for any additive functor (**Stacks 015E**);
* the unit of `R(g')^*` at `K` — invertible for the same reason:  no exactness of `(g')^*` is
  needed, and the statements below do not assume it;
* the unit of `Rf'_*` at `(g')^*K` — invertible because `(g')^*K` is again a complex of
  injectives, which is where the hypothesis on `(g')^*` is used, and only there;
* invertibility of the degree-zero map on each term of `K`, which is the hypothesis.

*Why the hypothesis is the degree-zero map at the ringed-topoi seating and not the modules
development's.*  What the development has for an étale square is
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModuleEtaleBaseChangeHFace.lean`), invertibility of
`AlgebraicGeometry.Space.moduleBaseChangeMap`, whose type is written with
`AlgebraicGeometry.Space.modulePushforward`.  The hypothesis below is about
`AlgebraicGeometry.Space.toposModuleBaseChangeMap`, written with
`AlgebraicGeometry.Space.toposModulePushforward`.  The two direct images differ by
`AlgebraicGeometry.Space.modulePushforwardIso`, and the two base change maps **are** identified
across it, by `AlgebraicGeometry.Space.toposModuleBaseChangeMap_eq_moduleBaseChangeMap` and its
componentwise form `AlgebraicGeometry.Space.toposModuleBaseChangeMap_app_eq`:  both are mates, of
the two comparisons of composite direct images at the two seatings, and the compatibility of the
mate construction with that comparison is
`Stacks.Cohomology.BaseChange.mate_ofNatIsoRight`.  So nothing separates the hypothesis below
from the étale case, and
`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale` draws the
conclusion:  for a cartesian square with `g` étale the derived base change map is invertible at
every object of `D⁺(𝒪_X)`, unconditionally.

*This is not Stacks 073K, part (1).*  Part (1) asserts invertibility for `g` merely **flat** and
`f` quasi-compact and quasi-separated.  The hypothesis below is invertibility of the degree-zero
base change map, which for a flat `g` holds only for *quasi-coherent* coefficients
(`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat`), and injective `𝒪_X`-modules
are not quasi-coherent — so this file does not give the flat case, and the flat case is not a
corollary of it.  That is the reason the source proves part (1) by reducing to an affine base and
writing `B` as a filtered colimit of finite free `A`-modules, rather than by Leray's acyclicity
lemma.  No `@[stacks 073K]` attribute is carried here.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard enoughInjectives_modules

/-- A natural transformation invertible at an object is invertible at every isomorphic object:
naturality writes the second component as the first conjugated by the images of the
isomorphism. -/
private theorem isIso_app_of_iso {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] {F G : 𝒞 ⥤ 𝒟}
    (α : F ⟶ G) {A A' : 𝒞} (e : A ≅ A') (h : IsIso (α.app A)) : IsIso (α.app A') := by
  have heq : α.app A' = F.map e.inv ≫ α.app A ≫ G.map e.hom := by
    rw [← α.naturality e.hom, ← Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id,
      Category.id_comp]
  rw [heq]
  have := h
  infer_instance

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y Y' : AlgebraicSpaces B S hS}

/-! ### The inverse image along an étale morphism preserves injectives -/

/-- **Stacks 03F3, part (1) at `AlgebraicGeometry.Space.modulePullback`.**  The inverse image of
`𝒪`-modules along an étale morphism of algebraic spaces carries injective objects to injective
objects.

This is `AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`, which
is stated for the étale-restriction spelling of the inverse image, transported along the
comparison of **Stacks 03LW**
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`;  injectivity is invariant under
isomorphism, so the transport costs nothing. -/
theorem preservesInjectiveObjects_modulePullback_of_isEtale (i : X' ⟶ X)
    (hi : IsEtale B S hS i.hom) :
    (modulePullback B S hS i).PreservesInjectiveObjects where
  injective_obj {M} hM := by
    have := preservesInjectiveObjects_etaleModulePullback B S hS i hi
    have h : Injective ((etaleModulePullback.{u, u} B S hS i hi).obj M) :=
      Functor.injective_obj_of_injective _ hM
    exact Injective.of_iso ((modulePullbackIsoEtaleModulePullback B S hS i hi).app M).symm h

/-! ### From the degree-zero base change map to the derived one -/

section Square

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]
    [PreservesFiniteLimits (modulePullback B S hS g')]
    [PreservesFiniteColimits (modulePullback B S hS g')]

omit [PreservesFiniteLimits (modulePullback B S hS g')]
  [PreservesFiniteColimits (modulePullback B S hS g')] in
/-- **The base change map of Stacks 0736 on `D⁺` is invertible as soon as the degree-zero base
change map of the square is invertible at every injective `𝒪_X`-module and `(g')^*` preserves
injective objects.**  The conclusion is invertibility at *every* object of `D⁺(𝒪_X)`, not only at
a module placed in degree zero.

Leray's acyclicity lemma:  an object of `D⁺(𝒪_X)` is the image of a bounded below complex `K` of
injective `𝒪_X`-modules, at which the three derived-functor units of
`Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_of_acyclic` are invertible — the terms of `K`
are injective (for `Rf_*` and `R(g')^*` alike), and `(g')^*K` is again a complex of injectives —
while the fourth hypothesis of that criterion, invertibility of the degree-zero map on the terms
of `K`, is the hypothesis here.

Injectivity of the coefficient is the *only* thing the hypothesis is asked at, which is what makes
this statement the measure of the distance between degree zero and `D⁺`;  and it is also exactly
why **Stacks 073K**, part (1) for a merely flat `g` is not a corollary, the degree-zero
clause `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat` being available only at
quasi-coherent coefficients.

The exactness binders are the ones `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap` is
itself defined against;  for flat morphisms they are **Stacks 04JC**, through
`AlgebraicGeometry.Space.exactFunctor_modulePullback_of_isFlat`. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_of_isIso_toposModuleBaseChangeMap_app_injective
    (comm : g' ≫ f = f' ≫ g)
    [(modulePullback B S hS g').PreservesInjectiveObjects]
    (hcomp : ∀ N : Modules.{u, u} B S hS X.1 X.2, Injective N →
      IsIso ((toposModuleBaseChangeMap f g f' g' comm).app N))
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) := by
  obtain ⟨n, hn⟩ := M.2
  have hMn : M.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff M n).1 hn
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso M n
  refine isIso_app_of_iso _ (Stacks.InjectiveModel.plusQhIsoPlusQ
    ((InjectiveObject.ι (Modules.{u, u} B S hS X.1 X.2)).mapCochainComplexPlus.obj L) ≪≫ e) ?_
  have hinj : ∀ i : ℤ, Injective (((HomotopyCategory.Plus.quotient
      (Modules.{u, u} B S hS X.1 X.2)).obj
      ((InjectiveObject.ι (Modules.{u, u} B S hS X.1 X.2)).mapCochainComplexPlus.obj
        L)).obj.as.X i) := fun _ => inferInstance
  refine Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_of_acyclic
    (toposModulePushforward f) (toposModulePushforward f') (modulePullback B S hS g)
    (modulePullback B S hS g') (toposModuleBaseChangeMap f g f' g' comm)
    (asIso (modulePullback B S hS g).rightDerivedFunctorPlusUnith) _ ?_ ?_ ?_ ?_
  · infer_instance
  · infer_instance
  · have hinj' : ∀ i : ℤ, Injective ((((modulePullback B S hS g').mapHomotopyCategoryPlus).obj
        ((HomotopyCategory.Plus.quotient (Modules.{u, u} B S hS X.1 X.2)).obj
          ((InjectiveObject.ι (Modules.{u, u} B S hS X.1 X.2)).mapCochainComplexPlus.obj
            L))).obj.as.X i) := fun i =>
      Functor.injective_obj_of_injective (modulePullback B S hS g') (hinj i)
    infer_instance
  · intro i
    exact hcomp _ (hinj i)

omit [PreservesFiniteLimits (modulePullback B S hS g')]
  [PreservesFiniteColimits (modulePullback B S hS g')] in
/-- **The base change map of Stacks 0736 on `D⁺` is invertible as soon as the degree-zero base
change map of the square is invertible and `(g')^*` preserves injective objects.**  The previous
statement with its hypothesis taken at every coefficient rather than at the injective ones;  it is
the form a consumer that has the degree-zero map invertible as a natural transformation uses. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_of_isIso_toposModuleBaseChangeMap
    (comm : g' ≫ f = f' ≫ g)
    [(modulePullback B S hS g').PreservesInjectiveObjects]
    (hcomp : IsIso (toposModuleBaseChangeMap f g f' g' comm))
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) := by
  refine isIso_toposModuleDerivedBaseChangeMap_app_of_isIso_toposModuleBaseChangeMap_app_injective
    f g f' g' comm (fun N _ => ?_) M
  have := hcomp
  exact NatIso.isIso_app_of_isIso _ N

omit [PreservesFiniteLimits (modulePullback B S hS g')]
  [PreservesFiniteColimits (modulePullback B S hS g')] in
/-- **For a square whose source leg is étale, the derived base change map of Stacks 0736 is
invertible as soon as the degree-zero one is.**  The inverse image along an étale morphism
preserves injective objects, so the hypothesis on `(g')^*` of the previous statement is
discharged.

For a *cartesian* square with `g` étale the source leg `g'` is étale as well, and invertibility
of `AlgebraicGeometry.Space.toposModuleBaseChangeMap` for such a square is available:  it is
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale` read through
`AlgebraicGeometry.Space.toposModuleBaseChangeMap_app_eq`.  So the étale case is unconditional,
and is drawn as
`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale`. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale_source (comm : g' ≫ f = f' ≫ g)
    (hg' : IsEtale B S hS g'.hom)
    (hcomp : IsIso (toposModuleBaseChangeMap f g f' g' comm))
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) :=
  have := preservesInjectiveObjects_modulePullback_of_isEtale g' hg'
  isIso_toposModuleDerivedBaseChangeMap_app_of_isIso_toposModuleBaseChangeMap f g f' g' comm
    hcomp M

end Square

end AlgebraicGeometry.Space

end
