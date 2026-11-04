module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A natural transformation out of `ModuleCat R` is determined by its value at `R`

The category `ModuleCat.{u} R` is generated under `u`-small colimits by the single object
`ModuleCat.of R R`: every module is the cokernel of a map between free modules, and a free
module is a coproduct of copies of `R`. This file turns that into an extensionality principle:
two natural transformations `Φ, Ψ : F ⟶ G` between functors `ModuleCat.{u} R ⥤ D`, with `F`
preserving the colimits involved, are equal as soon as `Φ` and `Ψ` agree at `ModuleCat.of R R`.

Only `F` is asked to preserve colimits: the components of `Φ` and `Ψ` at a colimit are morphisms
*out of* `F` applied to that colimit, so it is the source functor whose colimit cocone has to stay
colimiting.

## Main definitions

* `ModuleCat.freePresentationπ`: the canonical surjection onto `M` from the free module on the
  elements of `M`.
* `ModuleCat.freePresentation`: the two-step free presentation of `M` as a short complex
  `(free R).obj (ker π) ⟶ (free R).obj M ⟶ M`, exact at the middle with epimorphic right-hand
  map, so that `M` is the cokernel of a map between free modules.

## Main results

* `ModuleCat.eq_app_free_of_eq_app_self`: two natural transformations which agree at
  `ModuleCat.of R R` agree at every free module, provided the source functor preserves
  coproducts indexed by types in `Type u`.
* `ModuleCat.natTrans_ext_of_eq_app_self`: **two natural transformations out of `ModuleCat.{u} R`
  which agree at `ModuleCat.of R R` are equal**, provided the source functor preserves finite
  colimits and `Type u`-indexed coproducts.
* `ModuleCat.natTrans_ext_of_eq_app_self_of_preservesColimits`: the same under the single
  hypothesis that the source functor preserves all `u`-small colimits.
* `ModuleCat.natTrans_ext_of_eq_app_self_of_adjunction`: the same for a source functor that is a
  left adjoint, the adjunction being given. This is the form to use on a composite of left
  adjoints, where the adjunctions compose and no preservation instance has to be synthesized for
  the composite.

## Implementation notes

The step "two morphisms out of a colimit which agree on the cocone are equal, and naturality
identifies their composites with the legs" is `StacksDraft.CompactDevissage.eq_app_of_isColimit`.
It is not imported here: that file sits on top of the triangulated-category and derived-category
towers, and this file is elementary. The step is a few lines of `IsColimit.hom_ext` and is carried
out once, in a private lemma below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R] {D : Type*} [Category* D] {F G : ModuleCat.{u} R ⥤ D}

/-! ### The free presentation of a module -/

section Presentation

variable (M : ModuleCat.{u} R)

/-- The canonical surjection onto `M` from the free module on the elements of `M`: it sends the
generator indexed by `m` to `m`. -/
def freePresentationπ : (free R).obj ↥M ⟶ M := freeDesc (TypeCat.ofHom (id : ↥M → ↥M))

/-- `ModuleCat.freePresentationπ` sends the generator indexed by `m` to `m`. -/
@[simp]
theorem freePresentationπ_freeMk (m : M) : freePresentationπ M (freeMk m) = m :=
  freeDesc_apply _ _

/-- The canonical map `ModuleCat.freePresentationπ M` is an epimorphism. -/
instance epi_freePresentationπ : Epi (freePresentationπ M) := by
  rw [ModuleCat.epi_iff_surjective]
  exact fun m => ⟨freeMk m, freePresentationπ_freeMk M m⟩

/-- **The two-step free presentation of a module.** The right-hand map is the canonical surjection
`ModuleCat.freePresentationπ` from the free module on the elements of `M`, and the left-hand map
is the free module on the elements of its kernel, mapping the generator indexed by a relation to
that relation. It is exact at the middle (`ModuleCat.freePresentation_exact`) with epimorphic
right-hand map, so `M` is the cokernel of a map between free modules. -/
def freePresentation : ShortComplex (ModuleCat.{u} R) where
  X₁ := (free R).obj ↥(LinearMap.ker (freePresentationπ M).hom)
  X₂ := (free R).obj ↥M
  X₃ := M
  f := freeDesc (TypeCat.ofHom fun k : ↥(LinearMap.ker (freePresentationπ M).hom) =>
    (k : ↥((free R).obj ↥M)))
  g := freePresentationπ M
  zero := by
    ext k
    simp

/-- The right-hand object of the free presentation of `M` is `M`. -/
@[simp]
theorem freePresentation_X₃ : (freePresentation M).X₃ = M := rfl

/-- The right-hand map of the free presentation of `M` is `ModuleCat.freePresentationπ M`. -/
@[simp]
theorem freePresentation_g : (freePresentation M).g = freePresentationπ M := rfl

/-- The right-hand map of the free presentation of `M` is an epimorphism. -/
instance epi_freePresentation_g : Epi (freePresentation M).g :=
  epi_freePresentationπ M

/-- The free presentation of a module is exact at the middle: an element of the free module on the
elements of `M` which dies in `M` is a relation, hence the image of its own generator. -/
theorem freePresentation_exact : (freePresentation M).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact ⟨freeMk ⟨x, LinearMap.mem_ker.mpr hx⟩, freeDesc_apply _ _⟩

end Presentation

/-! ### The extensionality principle -/

section Ext

variable (Φ Ψ : F ⟶ G)

/-- Two natural transformations out of `F` agree at a colimit preserved by `F` as soon as they
agree at the objects of the diagram. -/
private theorem eq_app_pt_of_isColimit_of_forall_eq {J : Type*} [Category J]
    {K : J ⥤ ModuleCat.{u} R} {c : Cocone K} (hc : IsColimit c) [PreservesColimit K F]
    (h : ∀ j, Φ.app (K.obj j) = Ψ.app (K.obj j)) : Φ.app c.pt = Ψ.app c.pt :=
  (isColimitOfPreserves F hc).hom_ext fun j => by
    simp only [Functor.mapCocone_ι_app, Φ.naturality, Ψ.naturality, h]

/-- Two natural transformations out of `ModuleCat.{u} R` which agree at `ModuleCat.of R R` agree
at every free module: a free module is a coproduct of copies of `R`
(`ModuleCat.finsuppCoconeIsColimit`), `F` preserves that coproduct, and the two components are
determined on the images of its inclusions by naturality. -/
theorem eq_app_free_of_eq_app_self [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F]
    (h : Φ.app (ModuleCat.of R R) = Ψ.app (ModuleCat.of R R)) (X : Type u) :
    Φ.app ((free R).obj X) = Ψ.app ((free R).obj X) :=
  eq_app_pt_of_isColimit_of_forall_eq Φ Ψ (finsuppCoconeIsColimit R R X) fun _ => h

/-- **Two natural transformations out of `ModuleCat.{u} R` which agree at `ModuleCat.of R R` are
equal.** Every module is the cokernel of a map between free modules
(`ModuleCat.freePresentation`), free modules are coproducts of copies of `R`, and `F` preserves
both colimits, so the two components are determined at every module by their common value at
`ModuleCat.of R R`.

Only the source functor `F` has to preserve colimits. -/
theorem natTrans_ext_of_eq_app_self [PreservesFiniteColimits F]
    [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F]
    (h : Φ.app (ModuleCat.of R R) = Ψ.app (ModuleCat.of R R)) : Φ = Ψ := by
  ext M
  refine eq_app_pt_of_isColimit_of_forall_eq Φ Ψ (freePresentation_exact M).gIsCokernel ?_
  rintro (_ | _) <;> exact eq_app_free_of_eq_app_self Φ Ψ h _

/-- **Two natural transformations out of `ModuleCat.{u} R` which agree at `ModuleCat.of R R` are
equal**, for a source functor preserving all `u`-small colimits.

Only `Type u`-indexed coproducts and finite colimits are used
(`ModuleCat.natTrans_ext_of_eq_app_self`); this form is stated because preservation of colimits
is usually recorded as the single hypothesis `PreservesColimitsOfSize`. -/
theorem natTrans_ext_of_eq_app_self_of_preservesColimits [PreservesColimitsOfSize.{u, u} F]
    (h : Φ.app (ModuleCat.of R R) = Ψ.app (ModuleCat.of R R)) : Φ = Ψ :=
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits.{u, u} F
  natTrans_ext_of_eq_app_self Φ Ψ h

/-- **Two natural transformations out of a left adjoint `ModuleCat.{u} R ⥤ D` which agree at
`ModuleCat.of R R` are equal.** A left adjoint preserves all colimits
(`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`), so this is
`ModuleCat.natTrans_ext_of_eq_app_self_of_preservesColimits`.

This is the form to use on a composite of left adjoints: the adjunctions compose by
`CategoryTheory.Adjunction.comp`, so no preservation instance has to be synthesized for the
composite. -/
theorem natTrans_ext_of_eq_app_self_of_adjunction {F' : D ⥤ ModuleCat.{u} R} (adj : F ⊣ F')
    (h : Φ.app (ModuleCat.of R R) = Ψ.app (ModuleCat.of R R)) : Φ = Ψ :=
  have : PreservesColimitsOfSize.{u, u} F := adj.leftAdjoint_preservesColimits
  natTrans_ext_of_eq_app_self_of_preservesColimits Φ Ψ h

end Ext

end ModuleCat

end
