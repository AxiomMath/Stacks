module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional

/-!
# The quotient of an algebra sheaf by a sheaf of ideals is the cokernel of that ideal

Let `F` be an algebraic space over a scheme `S`, let `A` be a sheaf of commutative
`𝒪_F`-algebras on its small étale site and let `I` be a sheaf of ideals of the sheaf of rings
underlying `A`.  The quotient `A/I` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient` is a *sheafification*, so
nothing about its sections over a chart is visible by inspection.  **This file identifies its
underlying `𝒪_F`-module with the cokernel of the inclusion of `I`**, and draws the two
consequences that identification was wanted for: quasi-coherence of `A/I`, and the identification
of its sections over an affine étale chart with the objectwise quotient `A(W)/I(W)`.

The ideal is a submodule of the *free rank-one* sheaf of modules over the sheaf of rings
underlying `A`, that is, of `A` viewed as a module over itself; the quotient's underlying module
is `A` viewed as an `𝒪_F`-module along its structure-algebra maps.  The first section below
restricts the scalars: the sections of `I` over a chart are an *ideal* of `A(U)`, hence in
particular stable under multiplication by `A.algebraMap U r`, which is exactly the `𝒪_F(U)`-action
on the underlying module.  That is the only content of the comparison — no sheaf condition has to
be rechecked, membership in the two submodules being the same predicate on the same sections.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.idealModule` and
  `AlgebraicGeometry.Space.AlgebraSheaf.idealModuleι`: **a sheaf of ideals of `A`, read as an
  `𝒪_F`-module together with its monomorphism into the underlying module of `A`.**
* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientShortComplex`: the short complex
  `I ⟶ A ⟶ A/I` of `𝒪_F`-modules.
* `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleIdealQuotientCokernelIso`: **the bridge**
  — the underlying `𝒪_F`-module of `A/I` is the cokernel of the inclusion of `I` into the
  underlying `𝒪_F`-module of `A`.
* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientSectionsRingEquiv`: **the sections of `A/I`
  over an affine étale chart `W` are `A(W)/I(W)`**, as a ring isomorphism.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.kerSubmodule_underlyingModuleMap_toIdealQuotient`: the
  sectionwise kernel of `A ⟶ A/I` on underlying modules **is** `I`.
* `AlgebraicGeometry.Space.AlgebraSheaf.isLocallySurjective_toIdealQuotient` and
  `AlgebraicGeometry.Space.AlgebraSheaf.isLocallySurjective_idealQuotientMapOfLE`: the quotient
  morphism `A ⟶ A/I` and the comparison `A/I ⟶ A/I'` of an inclusion of sheaves of ideals are
  locally surjective.  These two are stated here rather than in
  `StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem`, since the epimorphism they produce is what the bridge runs on.
* `AlgebraicGeometry.Space.AlgebraSheaf.exact_idealQuotientShortComplex`: `I ⟶ A ⟶ A/I` is
  exact.
* `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_idealQuotient`: **`A/I` is quasi-coherent
  as soon as `A` and `I` are.**
* `AlgebraicGeometry.Space.AlgebraSheaf.surjective_toIdealQuotient_app` and
  `AlgebraicGeometry.Space.AlgebraSheaf.bijective_idealQuotientSectionsLift`: the quotient
  morphism is surjective on the sections over an affine étale chart, and the induced map
  `A(W)/I(W) → (A/I)(W)` is bijective.
* `AlgebraicGeometry.Space.AlgebraSheaf.isFinitePresentation_idealQuotient`: **`A/I` is of finite
  presentation** when `A` is and the ideal of sections of `I` over every affine étale chart is
  finitely generated.

## Implementation notes

**Where the bridge comes from, and what it does not need.**  The two legs of the factorisation
`I ⟶ A ⟶ A/I` have the right properties after passing to modules: the inclusion of `I` is a
monomorphism because it is sectionwise injective, and `A ⟶ A/I` becomes an epimorphism because it
is locally surjective
(`AlgebraicGeometry.Space.AlgebraSheaf.epi_underlyingModuleMap_of_isLocallySurjective`).  The
complex is *exact*, and that is the one non-formal input: it says the kernel is exactly `I` and
not something larger, which is
`AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal_toIdealQuotient` in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientKernel`, proved there from
local injectivity of the comparison with the sheafification and locality of membership in a sheaf
of ideals.  With exactness in hand `cokernel.desc` of the factorisation is a monomorphism by
`CategoryTheory.ShortComplex.Exact.mono_cokernelDesc` and an epimorphism because the quotient
morphism factors through it, and `𝒪_F`-modules are balanced, so
`CategoryTheory.isIso_of_mono_of_epi` applies.  **No cohomology is used anywhere**, and no
sections of a sheafification are computed.

The passage from local surjectivity to surjectivity on the sections over an affine étale chart —
needed for `bijective_idealQuotientSectionsLift` and hence for the finite presentation statement —
is `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`, the restated form
of Descent, Proposition 03DW, which is unconditional in this tree: faithfully flat descent along a
finite affine étale refinement, with no Čech cohomology.

**The hypotheses are not cosmetic.**  Quasi-coherence of `A/I` needs quasi-coherence of *both*
the underlying module of `A` and of `I`, because that is what
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional` consumes, and neither is a
consequence of the other.  In particular this file does **not** discharge the quasi-coherence and
finite-presentation input that `AlgebraicGeometry.Space.`
`exists_directed_isFinite_isFinitePresentation_locallySurjective` carries in its `hsource`: that
hypothesis supplies no quasi-coherence of the ambient algebra sheaf and no finiteness of the
ideals, so substituting the hypotheses of the results below for its conjuncts would make it
*stronger*.  What this file changes is that a caller who has those four things — quasi-coherence
of the ambient algebra, quasi-coherence of each ideal, finite presentation of the ambient algebra
and finite generation of each ideal of sections — can now produce the conjuncts, with no further
mathematics.

**The abelian structure is selected by hand.**
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is removed at every declaration using it, as
in `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent`: that instance states
the abelian structure of `SheafOfModules.{max u v r w}`, whose module universe cannot be the `u` of
`AlgebraicGeometry.Space.Modules.{u, u}`, and left in place it is selected ahead of Mathlib's
`SheafOfModules.instAbelian` and the elaboration dies on a universe constraint.

**No `@[stacks]` attribute is claimed.**  The identification of the sections of a sheafified
quotient over an affine chart is an input of the constructions of Stacks 082A and Stacks 086Z, not
a numbered statement of either, and nothing of either tag becomes provable here on its own.

## References

* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### A sheaf of ideals, read as a submodule of the underlying module -/

/-- A sheaf of ideals of the sheaf of rings underlying `A`, read as an objectwise submodule of
the underlying `𝒪_F`-module of `A`.

The carrier over a chart is unchanged: the sections of `I` over it.  What has to be checked is
only that they form an `𝒪_F(U)`-submodule and not merely an `A(U)`-submodule, and they do because
the `𝒪_F(U)`-action on the underlying module is multiplication by `A.algebraMap U r`, under which
an ideal is stable. -/
def idealValSubmodule (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    (underlyingModule A).val.Submodule where
  obj U :=
    { carrier := {x : (underlyingModule A).val.obj U | x ∈ I.obj U}
      add_mem' := fun {a b} hx hy =>
        show a + b ∈ I.obj U from add_mem (s := I.obj U) hx hy
      zero_mem' := show (0 : (underlyingModule A).val.obj U) ∈ I.obj U from zero_mem _
      smul_mem' := fun r _ hx => (I.obj U).smul_mem (A.algebraMap U r) hx }
  map _ _ hx := I.map_mem _ hx

/-- Membership in the restricted-scalars reading of a sheaf of ideals is membership in the sheaf
of ideals: the two submodules have the same sections. -/
theorem mem_idealValSubmodule (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf)
    (U : (SmallEtale B S hS F)ᵒᵖ) (x : (underlyingModule A).val.obj U) :
    x ∈ (idealValSubmodule A I).obj U ↔ x ∈ I.obj U :=
  Iff.rfl

/-- A sheaf of ideals of the sheaf of rings underlying `A`, read as a submodule of the underlying
`𝒪_F`-module of `A`.  Its membership condition is local because that of `I` is: by
`AlgebraicGeometry.Space.AlgebraSheaf.mem_idealValSubmodule` the two conditions are the same
predicate on the same sections, so the sieve of arrows along which a section restricts into the
submodule is the same sieve. -/
def idealSubmodule (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    (underlyingModule A).Submodule where
  toSubmodule := idealValSubmodule A I
  isSheaf := fun {_} s hs => I.isSheaf s (by exact hs)

/-- **A sheaf of ideals of the sheaf of rings underlying `A`, as an `𝒪_F`-module.** -/
def idealModule (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    Modules.{u, u} B S hS F hF :=
  (idealSubmodule A I).toSheafOfModules

/-- **The inclusion of a sheaf of ideals into the underlying `𝒪_F`-module of `A`.** -/
def idealModuleι (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    idealModule A I ⟶ underlyingModule A :=
  (idealSubmodule A I).ι

/-- The inclusion of a sheaf of ideals is a monomorphism of `𝒪_F`-modules: it is sectionwise
injective. -/
instance (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    Mono (idealModuleι A I) :=
  inferInstanceAs (Mono (idealSubmodule A I).ι)

/-! ### The ideal is the kernel of the quotient morphism -/

/-- **The sectionwise kernel of the morphism of underlying modules of `A ⟶ A/I` is exactly
`I`.**

One inclusion is that the quotient morphism kills the sections of `I`; the other says the
quotient is by `I` and not by something larger, and is
`AlgebraicGeometry.Space.AlgebraSheaf.toIdealQuotient_app_eq_zero_iff`, the sectionwise form of
`AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal_toIdealQuotient`.  Both submodules being submodules
of the same sheaf of modules with the same ambient sections, the statement is an equality of
objectwise submodules. -/
theorem kerSubmodule_underlyingModuleMap_toIdealQuotient
    (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    idealSubmodule A I =
      _root_.SheafOfModules.kerSubmodule (underlyingModuleMap (A.toIdealQuotient I)) := by
  refine _root_.SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U => ?_)
  refine SetLike.ext fun x => ?_
  refine Iff.trans (mem_idealValSubmodule A I U x) ?_
  refine Iff.trans ?_ (_root_.SheafOfModules.mem_kerSubmodule _ U x).symm
  exact (toIdealQuotient_app_eq_zero_iff A I U x).symm

section Transport

variable {M N : Modules.{u, u} B S hS F hF}

/-- A submodule which *is* the sectionwise kernel of a morphism is killed by that morphism.
Stated for a submodule given by an equation rather than by construction, so that the
identification of the ideal with the kernel can be transported without rewriting under a
dependent proof. -/
theorem ι_comp_eq_zero_of_eq_kerSubmodule (q : M ⟶ N) (K : M.Submodule)
    (hK : K = _root_.SheafOfModules.kerSubmodule q) : K.ι ≫ q = 0 := by
  subst hK
  exact _root_.SheafOfModules.kerIota_comp q

/-- A submodule which *is* the sectionwise kernel of a morphism is a kernel of it in the category
of `𝒪_F`-modules.  This is `SheafOfModules.kerIsLimit` with the submodule given by an equation;
the kernel fork carries a proof whose type moves with the submodule, which is why the transport is
done by substitution here rather than by rewriting at the use site. -/
def isLimitKernelForkOfEqKerSubmodule (q : M ⟶ N) (K : M.Submodule)
    (hK : K = _root_.SheafOfModules.kerSubmodule q) (w : K.ι ≫ q = 0) :
    IsLimit (KernelFork.ofι K.ι w) := by
  subst hK
  exact _root_.SheafOfModules.kerIsLimit q

end Transport

/-- The inclusion of `I` followed by the morphism of underlying modules of `A ⟶ A/I` vanishes. -/
theorem idealModuleι_comp_underlyingModuleMap (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) :
    idealModuleι A I ≫ underlyingModuleMap (A.toIdealQuotient I) = 0 :=
  ι_comp_eq_zero_of_eq_kerSubmodule _ _ (kerSubmodule_underlyingModuleMap_toIdealQuotient A I)

/-- **The short complex `I ⟶ A ⟶ A/I` of `𝒪_F`-modules.** -/
def idealQuotientShortComplex (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    ShortComplex (Modules.{u, u} B S hS F hF) :=
  ShortComplex.mk (idealModuleι A I) (underlyingModuleMap (A.toIdealQuotient I))
    (idealModuleι_comp_underlyingModuleMap A I)

/-- **The inclusion of `I` is a kernel of the morphism of underlying modules of `A ⟶ A/I`**, by
`AlgebraicGeometry.Space.AlgebraSheaf.kerSubmodule_underlyingModuleMap_toIdealQuotient`. -/
def isLimitKernelForkIdealModuleι (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    IsLimit (KernelFork.ofι (idealQuotientShortComplex A I).f
      (idealQuotientShortComplex A I).zero) :=
  isLimitKernelForkOfEqKerSubmodule _ _
    (kerSubmodule_underlyingModuleMap_toIdealQuotient A I) _

/-! ### Local surjectivity of the quotient morphisms -/

/-- **The quotient morphism `A ⟶ A/I` is locally surjective.**  Its underlying morphism of
sheaves of rings is the objectwise quotient map, surjective on the sections over every chart by
`Stacks.Sites.toQuotientPresheaf_app_surjective`, followed by the comparison with the
sheafification, which is locally surjective because sheafification is. -/
theorem isLocallySurjective_toIdealQuotient (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      (A.toIdealQuotient I).right.hom := by
  have h : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      (Stacks.Sites.toQuotientPresheaf.{u, u + 1, u} I) :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (Stacks.Sites.toQuotientPresheaf_app_surjective.{u, u + 1, u} I)
  show Presheaf.IsLocallySurjective _
    (Stacks.Sites.toQuotientPresheaf.{u, u + 1, u} I ≫
      toSheafify (SmallEtale.topology B S hS F)
        (Stacks.Sites.quotientPresheaf.{u, u + 1, u} I))
  infer_instance

/-- **The comparison `A/I ⟶ A/I'` attached to an inclusion of sheaves of ideals is locally
surjective.**  Composed after the quotient morphism `A ⟶ A/I` it *is* the quotient morphism
`A ⟶ A/I'`, which is locally surjective, and a factor of a locally surjective morphism through
which it is written on the right is locally surjective. -/
theorem isLocallySurjective_idealQuotientMapOfLE {A : AlgebraSheaf.{u, u} B S hS F hF}
    {I I' : A.IdealSheaf} (h : I ≤ I') :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      (idealQuotientMapOfLE h).right.hom := by
  have h' : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      (A.toIdealQuotient I').right.hom := isLocallySurjective_toIdealQuotient A I'
  refine Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (f₁ := (A.toIdealQuotient I).right.hom)
    (f₂ := (idealQuotientMapOfLE h).right.hom)
    (f₃ := (A.toIdealQuotient I').right.hom) _ ?_
  exact congrArg (fun k : A.right ⟶ (A.idealQuotient I').right => k.hom)
    (congrArg Hom.right (toIdealQuotient_comp_idealQuotientMapOfLE A h))

/-- **The morphism of underlying `𝒪_F`-modules of the quotient morphism `A ⟶ A/I` is an
epimorphism**, local surjectivity of a morphism of sheaves of modules being the same thing as
being an epimorphism. -/
theorem epi_underlyingModuleMap_toIdealQuotient (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) :
    Epi (underlyingModuleMap (A.toIdealQuotient I)) :=
  epi_underlyingModuleMap_of_isLocallySurjective (A.toIdealQuotient I)
    (isLocallySurjective_toIdealQuotient A I)

/-! ### The bridge: the underlying module of `A/I` is the cokernel of `I` -/

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The short complex `I ⟶ A ⟶ A/I` of `𝒪_F`-modules is exact.**  Its first map is a kernel of
its second, which is the statement that the quotient morphism kills exactly the sections of
`I`. -/
theorem exact_idealQuotientShortComplex (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) : (idealQuotientShortComplex A I).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelForkIdealModuleι A I)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The underlying `𝒪_F`-module of `A/I` is the cokernel of the inclusion of `I` into the
underlying `𝒪_F`-module of `A`.**

The comparison is `CategoryTheory.Limits.cokernel.desc` of the quotient morphism, which kills
`I`.  It is a monomorphism because the complex `I ⟶ A ⟶ A/I` is exact
(`CategoryTheory.ShortComplex.Exact.mono_cokernelDesc`) and an epimorphism because the quotient
morphism — an epimorphism, being locally surjective — is written as the cokernel projection
followed by it; `𝒪_F`-modules are balanced, so `CategoryTheory.isIso_of_mono_of_epi` applies.

This is the identification that makes quasi-coherence of a sheafified quotient reachable: with it,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional` applies. -/
def underlyingModuleIdealQuotientCokernelIso (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) :
    cokernel (idealModuleι A I) ≅ underlyingModule (A.idealQuotient I) := by
  have hepig : Epi (idealQuotientShortComplex A I).g :=
    epi_underlyingModuleMap_toIdealQuotient A I
  have hmono : Mono (cokernel.desc (idealQuotientShortComplex A I).f
      (idealQuotientShortComplex A I).g (idealQuotientShortComplex A I).zero) :=
    (exact_idealQuotientShortComplex A I).mono_cokernelDesc
  have hepi : Epi (cokernel.desc (idealQuotientShortComplex A I).f
      (idealQuotientShortComplex A I).g (idealQuotientShortComplex A I).zero) :=
    epi_of_epi_fac (cokernel.π_desc (idealQuotientShortComplex A I).f
      (idealQuotientShortComplex A I).g (idealQuotientShortComplex A I).zero)
  have hiso : IsIso (cokernel.desc (idealQuotientShortComplex A I).f
      (idealQuotientShortComplex A I).g (idealQuotientShortComplex A I).zero) :=
    isIso_of_mono_of_epi _
  exact @asIso _ _ _ _ _ hiso

/-! ### Quasi-coherence of the quotient -/

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The quotient of a quasi-coherent algebra sheaf by a quasi-coherent sheaf of ideals is
quasi-coherent.**

Its underlying module is the cokernel of the inclusion of the ideal, and the cokernel of a
morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent with no hypothesis
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`).

Both hypotheses are used, and neither follows from the other: the cokernel assertion needs
quasi-coherence of the source and of the target of the morphism it is applied to. -/
theorem isQuasicoherent_idealQuotient (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) (hA : A.IsQuasicoherent)
    (hI : (idealModule A I).IsQuasicoherentOnSite) :
    (A.idealQuotient I).IsQuasicoherent := by
  have h₂ : (underlyingModule A).IsQuasicoherentOnSite := hA
  exact _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
    (underlyingModuleIdealQuotientCokernelIso A I)
    (isQuasicoherentOnSite_cokernel_unconditional B S hS F hF (idealModuleι A I))

/-! ### The sections of the quotient over an affine étale chart -/

/-- **The quotient morphism `A ⟶ A/I` is surjective on the sections over an affine étale
chart**, when `A` and `I` are quasi-coherent.

Only local surjectivity is formal — `A/I` is a sheafification — and the passage to the sections
over an affine chart is
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`,
the restated form of Descent, Proposition 03DW, unconditional in this tree by faithfully flat
descent and with no Čech cohomology.  Quasi-coherence of the target is supplied by
`AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_idealQuotient`. -/
theorem surjective_toIdealQuotient_app (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) (hA : A.IsQuasicoherent)
    (hI : (idealModule A I).IsQuasicoherentOnSite) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective ((A.toIdealQuotient I).right.hom.app (op W)).hom := by
  intro y
  obtain ⟨x, hx⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite
    (underlyingModuleMap (A.toIdealQuotient I)) (epi_underlyingModuleMap_toIdealQuotient A I)
    hA (isQuasicoherent_idealQuotient A I hA hI) W hW y
  exact ⟨x, hx⟩

/-- The kernel of the quotient morphism on the sections over a chart is the ideal of sections of
`I` there. -/
theorem ker_toIdealQuotient_app (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    RingHom.ker ((A.toIdealQuotient I).right.hom.app U).hom =
      Stacks.Sites.sectionIdeal I U :=
  Ideal.ext fun a => (RingHom.mem_ker).trans (toIdealQuotient_app_eq_zero_iff A I U a)

/-- **The sections of `A/I` over an affine étale chart `W` are `A(W)/I(W)`**: the ring
homomorphism out of the objectwise quotient induced by the quotient morphism is bijective.

Surjectivity is `AlgebraicGeometry.Space.AlgebraSheaf.surjective_toIdealQuotient_app`, hence
Descent 03DW; injectivity is that the quotient morphism kills only the sections of `I`, hence
`AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal_toIdealQuotient`.  This is the identification of
the sections of a sheafified quotient that the constructions of Stacks 082A and Stacks 086Z
consume. -/
theorem bijective_idealQuotientSectionsLift (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) (hA : A.IsQuasicoherent)
    (hI : (idealModule A I).IsQuasicoherentOnSite) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Bijective (Ideal.Quotient.lift (Stacks.Sites.sectionIdeal I (op W))
      ((A.toIdealQuotient I).right.hom.app (op W)).hom
      fun a ha => toIdealQuotient_apply_eq_zero A I (op W) a ha) := by
  refine ⟨RingHom.lift_injective_of_ker_le_ideal _ _ (ker_toIdealQuotient_app A I (op W)).le,
    fun z => ?_⟩
  obtain ⟨a, ha⟩ := surjective_toIdealQuotient_app A I hA hI W hW z
  exact ⟨Ideal.Quotient.mk _ a, (Ideal.Quotient.lift_mk _ _ _).trans ha⟩

/-- **The sections of `A/I` over an affine étale chart `W` are `A(W)/I(W)`**, as a ring
isomorphism. -/
def idealQuotientSectionsRingEquiv (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) (hA : A.IsQuasicoherent)
    (hI : (idealModule A I).IsQuasicoherentOnSite) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    (A.right.obj.obj (op W) ⧸ Stacks.Sites.sectionIdeal I (op W)) ≃+*
      (A.idealQuotient I).right.obj.obj (op W) :=
  RingEquiv.ofBijective _ (bijective_idealQuotientSectionsLift A I hA hI W hW)

/-! ### Finite presentation of the quotient -/

/-- **The quotient of an algebra sheaf of finite presentation by a sheaf of ideals whose sections
over the affine étale charts are finitely generated is of finite presentation.**

Over an affine chart the structure-algebra map of `A/I` is that of `A` followed by the quotient
morphism on sections, which is surjective by
`AlgebraicGeometry.Space.AlgebraSheaf.surjective_toIdealQuotient_app` and whose kernel is the
ideal of sections of `I`; so `RingHom.FinitePresentation.comp_surjective` applies.

This is where the finite generation of the ideals enters, which is why the quasi-coherence
statement above asks none of it. -/
theorem isFinitePresentation_idealQuotient (A : AlgebraSheaf.{u, u} B S hS F hF)
    (I : A.IdealSheaf) (hA : A.IsQuasicoherent)
    (hI : (idealModule A I).IsQuasicoherentOnSite) (hAfp : A.IsFinitePresentation)
    (hfg : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        (Stacks.Sites.sectionIdeal I (op W)).FG) :
    (A.idealQuotient I).IsFinitePresentation := by
  intro W hW
  rw [← comp_algebraMap (A.toIdealQuotient I) (op W)]
  refine RingHom.FinitePresentation.comp_surjective (hAfp W hW)
    (surjective_toIdealQuotient_app A I hA hI W hW) ?_
  rw [ker_toIdealQuotient_app]
  exact hfg W hW

end AlgebraicGeometry.Space.AlgebraSheaf

end
