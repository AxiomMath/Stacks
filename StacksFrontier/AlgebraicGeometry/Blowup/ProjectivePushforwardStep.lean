module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardTwistSquare

/-!
# Degree-one generation of the twisted global sections on the blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal with a chosen finite generating family
`x₀, …, x_m`, and `i : X ⟶ 𝐏 = Proj A[T₀, …, T_m]` the closed immersion of the blowup
`X = Proj(⨁ₙ Iⁿ)` into projective space coming from the polynomial presentation `ψ` of the Rees
algebra. This file transports **degree-one generation of the twisted global sections in large
degrees** from `𝐏` to `X`:

`Γ(X, 𝒪_X(1 + d)) = 𝒮₁ · Γ(X, 𝒪_X(d))` for all `d` above a threshold,

which is the hypothesis `hstep` of
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation` for
`𝒮 = Stacks.Blowup.reesGrading I`. It cannot be proved on `X` directly: the dévissage that proves
it on `𝐏` bottoms out in `Stacks.ProjectiveSpace.Cohomology`
`.exists_sum_homogeneousScalar_twistingSheaf`, the explicit computation of the sections of the
twisting sheaves, and on `X` that computation *is* [Stacks, Tag 0AG7], the conclusion sought.

## How the transport works

`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardTwistSquare.lean` proves the scalar
square for the degreewise comparison `(i_*𝒪_X)(d) ≅ i_*(𝒪_X(d))` by naturality of the projection
formula and of the left unitor. The finiteness statements on `𝐏` and on `X` are both about the
`ℱ`-twist spelling `ℱ ⊗ 𝒪(d)`, with `ℱ = i_*𝒪_X` on `𝐏` and `ℱ = 𝒪_X` on `X`. So the comparison
is needed with the unit tensor left in place on the source side as well,
`(i_*𝒪_X)(d) ≅ i_*(𝒪_X ⊗ 𝒪_X(d))`, and that is `Stacks.Blowup.pushforwardTwistUnitIso`: the same
projection-formula construction, applied to the degree-`d` comparison followed by the *inverse*
left unitor. Its square is then the general
`Stacks.Blowup.pushforwardUnitTensorIso_hom_naturality` at that comparison, and the one extra
input is `MonoidalCategory.leftUnitor_inv_naturality` — the scalar action being a morphism of
twisting sheaves, naturality of the unitor is all that is needed to move it past.

Read on global sections over `⊤` the square becomes
`Ψ_{i + d}(a · s) = (ψ a) · Ψ_d s`, where `Ψ_d : Γ(𝐏, (i_*𝒪_X)(d)) → Γ(X, 𝒪_X(d))` is the
comparison's effect on sections — a bijection, since the comparison is an isomorphism and
sections of a direct image over the whole target are the sections of the source. Degree-one
generation then transports by one application of `AddSubgroup.closure_le`: a generator
`a · t` of `Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.degreeOneSections` on `𝐏` goes to the
generator `(ψ a) · Ψ_d t` on `X`, the degree-one element `ψ a` of the Rees grading being the
image of the degree-one form `a`.

## Main results

The elided prefix is `Stacks.Blowup`.

* `pullbackTwistUnitIso` and `pullbackTwistUnitIso_square`: [Stacks, Tag 01N1] part (3)'s
  comparison `(Proj ψ)^*𝒪(d) ≅ 𝒪(d)` with the inverse left unitor appended, and its scalar
  square.
* `pushforwardTwistUnitIso` and `pushforwardTwistUnitIso_square`: the degreewise comparison
  `(π_*𝒪)(d) ≅ π_*(𝒪 ⊗ 𝒪(d))` with both sides written as twists of the unit, and its scalar
  square — for an arbitrary graded surjection `ψ` whose `AlgebraicGeometry.Proj.map` is a closed
  immersion.
* `twistedSectionsUnitMap`, `twistedSectionsUnitMap_surjective` and
  `twistedSectionsUnitMap_homogeneousScalar`: the same on global sections.
* `mem_degreeOneSections_twistedSectionsUnitMap`: degree-one combinations transport.
* `exists_forall_mem_degreeOneSections_reesGrading`: **`hstep` on the blowup**, in the subgroup
  form. Composed with the general
  `Stacks.ProjectiveSpace.Cohomology.subset_span_grading_of_forall_mem_degreeOneSections` it is
  `hstep` in the graded-span form that
  `Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation`
  consumes. That composition is deliberately *not* given a name here: writing
  `Submodule.span (reesAlgebra I) …` into a statement makes instance search for
  `Module ↥(reesAlgebra I) (⨁ₙ Γ(X, 𝒪_X(n)))` explore the `Subalgebra` carrier's many module
  paths and exceed the heartbeat budget, whereas the general lemma's own statement — where the
  scalar ring is a variable — instantiates at no cost.

## Implementation notes

All the carriers are taken in one universe `Type u`, as in
`StacksFrontier/AlgebraicGeometry/ProjMapTwistDegreeSection/Basic.lean`: at mixed universes even
elaborating `(Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).obj (twistingSheaf 𝒮 n)`
exhausts the heartbeat budget.

`Stacks.Blowup.twistObj` reads the twisting sheaf at the `AlgebraicGeometry.Scheme.Modules`
spelling of the category of modules, so that the left unitor and its naturality are found at the
single monoidal instance `Stacks.Blowup.modulesMonoidal`. Without it the twisting sheaf's own
`sheafCompose` spelling asks for a second, separately declared instance on the same category.

The reassociations are explicit `Category.assoc` steps and the unitor's naturality is applied
through `congrArg` rather than by `rw`: the statements mix the two spellings of the category and
`rw` reports the goal as not type-correct at `implicit` transparency.

`Stacks.Blowup.exists_forall_mem_degreeOneSections_reesGrading` performs the instantiation of
`Stacks.Blowup.pushforwardTwistUnitIso_square` at `ψ = Stacks.Blowup.reesPresentation I x hx`
*inside its proof*. That instantiation does not typecheck as a theorem of its own — the kernel
exceeds its deterministic reduction budget on the instantiated type, Mathlib's
`AlgebraicGeometry.Proj.map` being declared with the transparency-respecting defeq check disabled
because it does not reduce affordably; see the module docstring of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardTwistSquare.lean`. Inside a larger
proof the surrounding context fixes the elaboration order and it goes through.

## References

* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules)
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistSheafScalarMap)
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection (pullbackTwistIso)

universe u

namespace Stacks.Blowup

attribute [local instance] modulesMonoidal modulesMonoidal'

section General

variable {S B' σ τ : Type u} [CommRing S] [CommRing B'] [SetLike σ S] [AddSubgroupClass σ S]
  [SetLike τ B'] [AddSubgroupClass τ B'] (𝒮 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒮] [GradedRing ℬ]

/-- The `d`-th twisting sheaf read in the `AlgebraicGeometry.Scheme.Modules` spelling. -/
public abbrev twistObj (d : ℤ) : (AlgebraicGeometry.Proj ℬ).Modules := twistingSheaf ℬ d

/-- **The `d`-th twist of the structure sheaf is the unit tensor the `d`-th twisting sheaf.**
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` is the sheafified tensor product
in the `Stacks.SheafOfModules.TensorSheafification` spelling and `⊗` is the monoidal product in
the `Stacks.SheafOfModules.TensorStalkRingedSpace` spelling; naming this equation isolates the
unfolding between them, which is expensive to re-check inside a larger unification problem. -/
public theorem twistSheafOfModules_unit_eq (d : ℤ) :
    twistSheafOfModules ℬ (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) d =
      𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ⊗ twistObj ℬ d := rfl

/-- **Multiplication by a homogeneous scalar on the twist of the structure sheaf is a
whiskering.** This is `Stacks.Blowup.whiskerLeft_eq_tensorSheafMap` read through the definition of
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap`; it is what lets the unitor's
naturality be applied to the scalar action. -/
public theorem twistSheafScalarMap_unit_eq (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k) (b : ℬ i) :
    twistSheafScalarMap ℬ (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)
        i n k hk b =
      (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ◁ twistScalarSheafMap ℬ i n k hk b) :=
  (twistSheafScalarMap_eq_tensorSheafMap ℬ
      (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) i n k hk b).trans
    (whiskerLeft_eq_tensorSheafMap (AlgebraicGeometry.Proj ℬ).toRingedSpace
      (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules) (twistScalarSheafMap ℬ i n k hk b)).symm

variable (ψ : 𝒮 →+*ᵍ ℬ)
  (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
  (hsurj : Function.Surjective (ψ : S → B'))
  (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
  [IsClosedImmersion (AlgebraicGeometry.Proj.map ψ hψ)]

/-- The degree-`d` comparison with the unit tensor folded into the target. -/
public def pullbackTwistUnitIso (d : ℤ) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).obj (twistingSheaf 𝒮 d) ≅
      𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ⊗ twistObj ℬ d :=
  pullbackTwistIso ψ hψ hsurj hgen d ≪≫ (λ_ (twistObj ℬ d)).symm

omit [IsClosedImmersion (AlgebraicGeometry.Proj.map ψ hψ)] in
/-- **The degree-`d` comparison with the inverse unitor appended still intertwines the graded
scalar action.** The scalar action is a morphism `𝒪(d) ⟶ 𝒪(i + d)` of twisting sheaves, so
appending the inverse left unitor costs exactly one naturality square,
`MonoidalCategory.leftUnitor_inv_naturality`, on top of
`Stacks.AlgebraicGeometry.ThetaMultiplicative.pullbackTwistIso_twistScalarSheafMap`. -/
public theorem pullbackTwistUnitIso_square (i : ℕ) (d : ℤ) (a : 𝒮 i) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
          (twistScalarSheafMap 𝒮 i d ((i : ℤ) + d) rfl a) ≫
        (pullbackTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen ((i : ℤ) + d)).hom =
      (pullbackTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).hom ≫
        (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ◁
          twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩) :=
  calc (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
          (twistScalarSheafMap 𝒮 i d ((i : ℤ) + d) rfl a) ≫
        ((pullbackTwistIso ψ hψ hsurj hgen ((i : ℤ) + d)).hom ≫
          (λ_ (twistObj ℬ ((i : ℤ) + d))).inv)
      = ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
            (twistScalarSheafMap 𝒮 i d ((i : ℤ) + d) rfl a) ≫
          (pullbackTwistIso ψ hψ hsurj hgen ((i : ℤ) + d)).hom) ≫
        (λ_ (twistObj ℬ ((i : ℤ) + d))).inv := (Category.assoc _ _ _).symm
    _ = ((pullbackTwistIso ψ hψ hsurj hgen d).hom ≫
          twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩) ≫
        (λ_ (twistObj ℬ ((i : ℤ) + d))).inv := by
          rw [Stacks.AlgebraicGeometry.ThetaMultiplicative.pullbackTwistIso_twistScalarSheafMap
            𝒮 ℬ ψ hψ hsurj hgen i d a]
    _ = (pullbackTwistIso ψ hψ hsurj hgen d).hom ≫
        (twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩ ≫
          (λ_ (twistObj ℬ ((i : ℤ) + d))).inv) := Category.assoc _ _ _
    _ = (pullbackTwistIso ψ hψ hsurj hgen d).hom ≫
        ((λ_ (twistObj ℬ d)).inv ≫ (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ◁
          twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩)) :=
          congrArg (fun t => (pullbackTwistIso ψ hψ hsurj hgen d).hom ≫ t)
            (MonoidalCategory.leftUnitor_inv_naturality
              (X := twistObj ℬ d) (Y := twistObj ℬ ((i : ℤ) + d))
              (twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩))
    _ = ((pullbackTwistIso ψ hψ hsurj hgen d).hom ≫ (λ_ (twistObj ℬ d)).inv) ≫
        (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ◁
          twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩) :=
          (Category.assoc _ _ _).symm

/-- The degree-`d` comparison `(π_*𝒪)(d) ≅ π_*(𝒪(d))`, with both sides written as twists of
the unit. -/
public def pushforwardTwistUnitIso (d : ℤ) :
    twistSheafOfModules 𝒮 ((Scheme.Modules.pushforward
          (AlgebraicGeometry.Proj.map ψ hψ)).obj
          (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d ≅
      (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
        (twistSheafOfModules ℬ
          (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) d) :=
  pushforwardUnitTensorIso (AlgebraicGeometry.Proj.map ψ hψ) (twistingSheaf 𝒮 d)
    (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ⊗ twistObj ℬ d)
    (pullbackTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d)

/-- **The degreewise comparison intertwines the graded scalar action, with both sides written as
twists of the structure sheaf.** For a graded surjection `ψ : 𝒮 →+*ᵍ ℬ` generated in degree one
whose induced morphism `π = Proj ψ` is a closed immersion and every homogeneous `a` of degree `i`,

`(a ·) ≫ Φ_{i + d} = Φ_d ≫ π_*((ψ a) ·)`,

where `Φ_d = pushforwardTwistUnitIso` is the comparison `(π_*𝒪)(d) ≅ π_*(𝒪 ⊗ 𝒪(d))`. This is
`Stacks.Blowup.pushforwardUnitTensorIso_hom_naturality` at `pullbackTwistUnitIso`, and it is the
form `Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation`
consumes: both its hypotheses are about the `ℱ`-twist spelling, with `ℱ` the structure sheaf on
the source and its direct image on the target. -/
public theorem pushforwardTwistUnitIso_square (i : ℕ) (d : ℤ) (a : 𝒮 i) :
    twistSheafScalarMap 𝒮 ((Scheme.Modules.pushforward
            (AlgebraicGeometry.Proj.map ψ hψ)).obj
            (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf))
          i d ((i : ℤ) + d) rfl a ≫
        (pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen ((i : ℤ) + d)).hom =
      (pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).hom ≫
        (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).map
          (twistSheafScalarMap ℬ
            (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)
            i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩) := by
  refine Eq.trans ?_ (congrArg
    (fun t : (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ⊗ twistObj ℬ d) ⟶
        (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ⊗ twistObj ℬ ((i : ℤ) + d)) =>
      (pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).hom ≫
        (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).map t)
    (twistSheafScalarMap_unit_eq ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩).symm)
  exact pushforwardUnitTensorIso_hom_naturality (AlgebraicGeometry.Proj.map ψ hψ)
    (pullbackTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d)
    (pullbackTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen ((i : ℤ) + d))
    (twistScalarSheafMap 𝒮 i d ((i : ℤ) + d) rfl a)
    (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ◁
      twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩)
    (pullbackTwistUnitIso_square 𝒮 ℬ ψ hψ hsurj hgen i d a)

/-- The degree-`d` comparison read on global sections, as a bare function. -/
public def twistedSectionsUnitMap (d : ℤ) :
    Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent 𝒮
        ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
          (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d →
      Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent ℬ
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) d :=
  fun s => (((pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).hom.val.app (op ⊤)).hom s)

/-- **The comparison is surjective on global sections**, the inverse isomorphism providing the
preimage. -/
public theorem twistedSectionsUnitMap_surjective (d : ℤ) :
    Function.Surjective (twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d) := fun u =>
  ⟨(((pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).inv.val.app (op ⊤)).hom u),
    congrArg (fun α => (α.val.app (op ⊤)).hom u)
      (pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).inv_hom_id⟩

/-- **The comparison is additive on global sections**, being the global sections of a morphism of
sheaves of modules. -/
public theorem twistedSectionsUnitMap_add (d : ℤ)
    (s t : Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent 𝒮
      ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d) :
    twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d (s + t) =
      twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d s +
        twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d t :=
  map_add ((pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).hom.val.app (op ⊤)).hom s t

/-- **The square on global sections:** `Ψ_{i + d}(a · s) = (ψ a) · Ψ_d s`, for an arbitrary
global section `s` of `(π_*𝒪)(d)`. It is the sheaf-level square evaluated over `⊤`; the sections
of a direct image over the whole target being the sections of the source
(`Stacks.Cohomology.AffineBase.pushforwardSectionsIso`, which is the identity), no further
comparison intervenes. -/
public theorem twistedSectionsUnitMap_homogeneousScalar (i : ℕ) (d : ℤ) (a : 𝒮 i)
    (s : Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent 𝒮
      ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d) :
    twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen ((i : ℤ) + d)
        (Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections 𝒮
          ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
            (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) i d a s) =
      Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections ℬ
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) i d
        ⟨ψ a, ψ.map_mem a.2⟩ (twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d s) :=
  congrArg (fun α => (α.val.app (op ⊤)).hom s)
    (pushforwardTwistUnitIso_square 𝒮 ℬ ψ hψ hsurj hgen i d a)

/-- The comparison on global sections, as an additive homomorphism. -/
public def twistedSectionsUnitAddHom (d : ℤ) :
    Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent 𝒮
        ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
          (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d →+
      Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent ℬ
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) d :=
  ((pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).hom.val.app (op ⊤)).hom.toAddMonoidHom

/-- The additive homomorphism of
`Stacks.Blowup.twistedSectionsUnitAddHom` is the function of
`Stacks.Blowup.twistedSectionsUnitMap`. -/
public theorem twistedSectionsUnitAddHom_apply (d : ℤ)
    (s : Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent 𝒮
      ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d) :
    twistedSectionsUnitAddHom 𝒮 ℬ ψ hψ hsurj hgen d s =
      twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d s := rfl

/-- **Degree-one combinations transport along the comparison.** A generator `a · t` of the
degree-one combinations on `Proj 𝒮` goes to the generator `(ψ a) · Ψ_d t` on `Proj ℬ`, the
degree-one element `ψ a` of `ℬ` being the image of the degree-one element `a` of `𝒮`; the rest is
`AddSubgroup.closure_le` into the comap of the target subgroup. -/
public theorem mem_degreeOneSections_twistedSectionsUnitMap (d : ℤ)
    {s : Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent 𝒮
      ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) ((1 : ℤ) + d)}
    (hs : s ∈ Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.degreeOneSections 𝒮
      ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d) :
    twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen ((1 : ℤ) + d) s ∈
      Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.degreeOneSections ℬ
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) d := by
  refine (AddSubgroup.closure_le (AddSubgroup.comap
    (twistedSectionsUnitAddHom 𝒮 ℬ ψ hψ hsurj hgen ((1 : ℤ) + d))
    (Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.degreeOneSections ℬ
      (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) d))).mpr ?_ hs
  rintro z ⟨a, t, rfl⟩
  exact AddSubgroup.subset_closure
    ⟨⟨ψ a, ψ.map_mem a.2⟩, twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d t,
      twistedSectionsUnitMap_homogeneousScalar 𝒮 ℬ ψ hψ hsurj hgen 1 d a t⟩

end General

section Blowup

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.ProjectiveCohomology (polyGrading)

/-- **[Stacks, Tag 01YS] clause (5)'s hypothesis `hstep`, on the blowup**, in the subgroup form:
for `A` Noetherian, `I ⊆ A` an ideal with a finite generating family and `X` the blowup of
`Spec A` in `I`, there is a `B` such that for every `d ≥ B` each global section of `𝒪_X(1 + d)` is
a combination of global sections of `𝒪_X(d)` with degree-one elements of the Rees algebra as
coefficients.

This is the statement that cannot be had on `X` directly, and it is obtained here by transporting
`Stacks.ProjectiveSpace.Cohomology.exists_forall_mem_degreeOneSections_of_isCoherent` for the
coherent sheaf `i_*𝒪_X` on `𝐏 = Proj A[T₀, …, T_m]` along
`Stacks.Blowup.twistedSectionsUnitMap`. -/
public theorem exists_forall_mem_degreeOneSections_reesGrading {A : Type u} [CommRing A]
    [IsNoetherianRing A] {I : Ideal A} {m : ℕ} (x : Fin (m + 1) → A) (hx : ∀ j, x j ∈ I)
    (hspan : I = Ideal.span (Set.range x)) :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d →
      ∀ u : Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent
        (reesGrading I) (SheafOfModules.unit (blowUpSpec I).ringCatSheaf) ((1 : ℤ) + d),
        u ∈ Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.degreeOneSections (reesGrading I)
          (SheafOfModules.unit (blowUpSpec I).ringCatSheaf) d := by
  have : IsClosedImmersion (AlgebraicGeometry.Proj.map (reesPresentation I x hx)
      (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
        (surjective_reesPresentation I x hx hspan))) :=
    isClosedImmersion_blowUpSpecToProjSpace I x hx hspan
  have : IsLocallyNoetherian (blowUpSpec I) :=
    isLocallyNoetherian_of_isClosedImmersion (blowUpSpecToProjSpace I x hx hspan)
  have : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit (blowUpSpec I).ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit (blowUpSpec I)
  obtain ⟨B, hB⟩ :=
    Stacks.ProjectiveSpace.Cohomology.exists_forall_mem_degreeOneSections_of_isCoherent A m
      ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
        (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))
      (isCoherent_pushforward_of_isClosedImmersion (blowUpSpecToProjSpace I x hx hspan)
        (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))
  refine ⟨B, fun d hd u => ?_⟩
  obtain ⟨s, rfl⟩ := twistedSectionsUnitMap_surjective (polyGrading A m) (reesGrading I)
    (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
    (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A m) ((1 : ℤ) + d) u
  exact mem_degreeOneSections_twistedSectionsUnitMap (polyGrading A m) (reesGrading I)
    (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
    (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A m) d (hB d hd s)

end Blowup

end Stacks.Blowup

end
