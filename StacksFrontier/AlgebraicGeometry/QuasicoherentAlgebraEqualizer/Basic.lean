module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# The equalizer of two morphisms of sheaves of algebras

Let `X` be a scheme and let `φ, ψ : A ⟶ B` be two morphisms of sheaves of commutative
`𝒪_X`-algebras. The sections over an open `U` on which `φ` and `ψ` agree form a subring
`eqSubring φ ψ U` of `A(U)`; these subrings are stable under the restriction maps of `A` and
assemble into a sheaf of commutative `𝒪_X`-algebras `equalizerAlgebra φ ψ`, the equalizer of
`φ` and `ψ` in the category of sheaves of `𝒪_X`-algebras.

## Main definitions

* `Stacks.QuasicoherentAlgebraEqualizer.eqSubring` — the subring of agreement on sections.
* `Stacks.QuasicoherentAlgebraEqualizer.eqPresheaf` — the presheaf of those subrings.
* `Stacks.QuasicoherentAlgebraEqualizer.equalizerAlgebra` — the resulting sheaf of
  `𝒪_X`-algebras, together with the inclusion `equalizerAlgebraι` into `A`.

## Main results

* `Stacks.QuasicoherentAlgebraEqualizer.isSheaf_eqPresheaf` — the presheaf of agreement
  subrings is a sheaf.
* `Stacks.QuasicoherentAlgebraEqualizer.isLimitFork` — `equalizerAlgebra φ ψ` is the equalizer
  of `φ` and `ψ` in the category of sheaves of `𝒪_X`-algebras.

## Implementation notes

The sheaf condition is the unique-gluing condition
`TopCat.Presheaf.IsSheafUniqueGluing`, which is available for `CommRingCat`-valued presheaves
because `CommRingCat` is concrete and complete and its forgetful functor preserves limits and
reflects isomorphisms. Existence of a gluing is the gluing in `A` of the underlying sections,
and it lies in the agreement subring because `B` is separated: the two images agree on each
member of the covering. Uniqueness is uniqueness in `A`, since the restriction maps of the
subring presheaf are restrictions of those of `A`.

The agreement condition is recorded as a `Subring` of the sections rather than as the categorical
equalizer in sheaves of rings, because everything downstream — the comparison with the
localization of the sections over an affine open, hence quasi-coherence — is a statement about
elements of the sections.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec

universe u

namespace Stacks.QuasicoherentAlgebraEqualizer

variable {X : Scheme.{u}} {A B : AlgebraSheaf X} (φ ψ : A ⟶ B)

/-! ### The subring of agreement on sections -/

/-- The subring of the sections of `A` over an open on which two morphisms of algebra sheaves
`φ, ψ : A ⟶ B` agree. -/
def eqSubring (U : (Opens X)ᵒᵖ) : Subring (A.right.obj.obj U) :=
  RingHom.eqLocus (φ.right.hom.app U).hom (ψ.right.hom.app U).hom

/-- A section of `A` lies in the subring of agreement exactly when `φ` and `ψ` agree on it. -/
theorem mem_eqSubring_iff {U : (Opens X)ᵒᵖ} (x : A.right.obj.obj U) :
    x ∈ eqSubring φ ψ U ↔
      (φ.right.hom.app U).hom x = (ψ.right.hom.app U).hom x :=
  Iff.rfl

/-- The map on sections of a morphism of algebra sheaves commutes with restriction. -/
theorem secMap_naturality {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (x : A.right.obj.obj U) :
    (φ.right.hom.app V).hom ((A.right.obj.map f).hom x) =
      (B.right.obj.map f).hom ((φ.right.hom.app U).hom x) := by
  have h := congr($(φ.right.hom.naturality f).hom x)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using h

/-- The restriction maps of `A` preserve the subring of agreement. -/
theorem map_mem_eqSubring {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) {x : A.right.obj.obj U}
    (hx : x ∈ eqSubring φ ψ U) : (A.right.obj.map f).hom x ∈ eqSubring φ ψ V := by
  rw [mem_eqSubring_iff] at hx ⊢
  rw [secMap_naturality φ f x, hx, ← secMap_naturality ψ f x]

/-! ### The presheaf of agreement subrings -/

/-- The presheaf of commutative rings whose sections over an open are the sections of `A` on
which `φ` and `ψ` agree. -/
def eqPresheaf : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of ↥(eqSubring φ ψ U)
  map {U V} f := CommRingCat.ofHom
    ((A.right.obj.map f).hom.restrict (eqSubring φ ψ U) (eqSubring φ ψ V)
      fun _ hx ↦ map_mem_eqSubring φ ψ f hx)
  map_id U := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

/-- The restriction maps of `eqPresheaf φ ψ` are those of `A` on underlying sections. -/
@[simp]
theorem eqPresheaf_map_val {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (x : ↥(eqSubring φ ψ U)) :
    (((eqPresheaf φ ψ).map f).hom x).val = (A.right.obj.map f).hom x.val :=
  rfl

/-! ### The sheaf condition -/

/-- The presheaf of agreement subrings is a sheaf: a compatible family glues in `A`, and the
gluing lies in the subring of agreement because `B` is separated. -/
theorem isSheaf_eqPresheaf :
    TopCat.Presheaf.IsSheaf (X := X) (eqPresheaf φ ψ) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hsfA : TopCat.Presheaf.IsCompatible A.right.obj U (fun i ↦ (sf i).val) := fun i j ↦
    congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, huniq⟩ := A.right.existsUnique_gluing U (fun i ↦ (sf i).val) hsfA
  have hsmem : s ∈ eqSubring φ ψ (op (iSup U)) := by
    rw [mem_eqSubring_iff]
    refine B.right.eq_of_locally_eq U _ _ fun i ↦ ?_
    rw [← secMap_naturality φ (Opens.leSupr U i).op s,
      ← secMap_naturality ψ (Opens.leSupr U i).op s]
    show (φ.right.hom.app (op (U i))).hom ((A.right.obj.map (Opens.leSupr U i).op).hom s) =
      (ψ.right.hom.app (op (U i))).hom ((A.right.obj.map (Opens.leSupr U i).op).hom s)
    rw [hs i]
    exact (sf i).2
  refine ⟨⟨s, hsmem⟩, fun i ↦ Subtype.ext (hs i), fun t ht ↦ Subtype.ext ?_⟩
  exact huniq t.val fun i ↦ congrArg Subtype.val (ht i)

/-- The equalizer of two morphisms of algebra sheaves, as a sheaf of commutative rings. -/
def eqSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨eqPresheaf φ ψ, isSheaf_eqPresheaf φ ψ⟩

/-! ### The algebra structure -/

/-- Equal morphisms of sheaves of rings agree on every section. -/
private theorem app_apply_congr {F G : TopCat.Sheaf CommRingCat.{u} X} {f g : F ⟶ G} (h : f = g)
    (U : (Opens X)ᵒᵖ) (x : F.obj.obj U) : (f.hom.app U).hom x = (g.hom.app U).hom x := by
  rw [h]

/-- The image of a section of the structure sheaf lies in the subring of agreement, because
`φ` and `ψ` are morphisms over `𝒪_X`. -/
theorem structureMap_mem_eqSubring (U : (Opens X)ᵒᵖ) (r : X.sheaf.obj.obj U) :
    (A.hom.hom.app U).hom r ∈ eqSubring φ ψ U := by
  rw [mem_eqSubring_iff]
  exact (app_apply_congr (Under.w φ) U r).trans (app_apply_congr (Under.w ψ) U r).symm

/-- The structure morphism of the equalizer algebra. -/
def eqStructureHom : X.sheaf ⟶ eqSheaf φ ψ :=
  ⟨{ app := fun U ↦ CommRingCat.ofHom
       ((A.hom.hom.app U).hom.codRestrict (eqSubring φ ψ U) (structureMap_mem_eqSubring φ ψ U))
     naturality := fun U V f ↦ by
       ext r
       exact Subtype.ext (congr($(A.hom.hom.naturality f).hom r)) }⟩

/-- The inclusion of the equalizer sheaf into `A`, as a morphism of sheaves of rings. -/
def eqSheafι : eqSheaf φ ψ ⟶ A.right :=
  ⟨{ app := fun U ↦ CommRingCat.ofHom (eqSubring φ ψ U).subtype
     naturality := fun U V f ↦ by ext x; rfl }⟩

/-- **The equalizer of two morphisms of sheaves of `𝒪_X`-algebras.** Its sections over an open
are the sections of `A` on which the two morphisms agree. -/
def equalizerAlgebra : AlgebraSheaf X :=
  Under.mk (eqStructureHom φ ψ)

/-- The sections of the equalizer algebra over an open are the subring of agreement. -/
theorem sections_equalizerAlgebra (U : X.Opens) :
    AlgebraSheaf.sections (equalizerAlgebra φ ψ) U =
      CommRingCat.of ↥(eqSubring φ ψ (op U)) :=
  rfl

/-- The inclusion of the equalizer algebra into `A`. -/
def equalizerAlgebraι : equalizerAlgebra φ ψ ⟶ A :=
  Under.homMk (eqSheafι φ ψ) (Sheaf.hom_ext (by ext U r; rfl))

/-- On sections, the inclusion of the equalizer algebra into `A` takes the underlying section. -/
@[simp]
theorem equalizerAlgebraι_app_apply (U : (Opens X)ᵒᵖ) (x : ↥(eqSubring φ ψ U)) :
    ((equalizerAlgebraι φ ψ).right.hom.app U).hom x = x.val :=
  rfl

/-- The inclusion of the equalizer algebra equalizes `φ` and `ψ`. -/
theorem equalizerAlgebraι_comp :
    equalizerAlgebraι φ ψ ≫ φ = equalizerAlgebraι φ ψ ≫ ψ := by
  ext
  refine Sheaf.hom_ext ?_
  ext U x
  exact x.2

/-! ### The universal property -/

section UniversalProperty

variable {C : AlgebraSheaf X}

/-- A morphism of algebra sheaves equalizing `φ` and `ψ` takes values in the subring of
agreement. -/
theorem comp_mem_eqSubring {f : C ⟶ A} (hf : f ≫ φ = f ≫ ψ) (U : (Opens X)ᵒᵖ)
    (c : C.right.obj.obj U) : (f.right.hom.app U).hom c ∈ eqSubring φ ψ U := by
  rw [mem_eqSubring_iff]
  exact app_apply_congr (congrArg (·.right) hf) U c

/-- The factorization of a morphism of algebra sheaves equalizing `φ` and `ψ` through the
equalizer. -/
def lift (f : C ⟶ A) (hf : f ≫ φ = f ≫ ψ) : C ⟶ equalizerAlgebra φ ψ :=
  Under.homMk
    (⟨{ app := fun U ↦ CommRingCat.ofHom
          ((f.right.hom.app U).hom.codRestrict (eqSubring φ ψ U) (comp_mem_eqSubring φ ψ hf U))
        naturality := fun U V g ↦ by
          ext c
          exact Subtype.ext (congr($(f.right.hom.naturality g).hom c)) }⟩ :
      C.right ⟶ eqSheaf φ ψ)
    (Sheaf.hom_ext (by
      ext U r
      have h : ((C.hom ≫ f.right).hom.app U).hom r = (A.hom.hom.app U).hom r := by
        rw [Under.w f]
      exact Subtype.ext h))

/-- On sections, the underlying section of the image of `c` under `lift φ ψ f hf` is its image
under `f`. -/
@[simp]
theorem lift_app_val (f : C ⟶ A) (hf : f ≫ φ = f ≫ ψ) (U : (Opens X)ᵒᵖ)
    (c : C.right.obj.obj U) :
    (((lift φ ψ f hf).right.hom.app U).hom c).val = (f.right.hom.app U).hom c :=
  rfl

/-- The factorization through the equalizer followed by the inclusion into `A` is the original
morphism. -/
theorem lift_comp_ι (f : C ⟶ A) (hf : f ≫ φ = f ≫ ψ) :
    lift φ ψ f hf ≫ equalizerAlgebraι φ ψ = f := by
  ext
  refine Sheaf.hom_ext ?_
  ext U c
  rfl

/-- Two morphisms into the equalizer agreeing after the inclusion into `A` are equal. -/
theorem hom_ext {g h : C ⟶ equalizerAlgebra φ ψ}
    (H : g ≫ equalizerAlgebraι φ ψ = h ≫ equalizerAlgebraι φ ψ) : g = h := by
  ext
  refine Sheaf.hom_ext ?_
  ext U c
  exact Subtype.ext (app_apply_congr (congrArg (·.right) H) U c)

/-- **`equalizerAlgebra φ ψ` is the equalizer of `φ` and `ψ` in the category of sheaves of
`𝒪_X`-algebras.** -/
def isLimitFork :
    IsLimit (Fork.ofι (equalizerAlgebraι φ ψ) (equalizerAlgebraι_comp φ ψ)) :=
  Fork.IsLimit.mk _ (fun s ↦ lift φ ψ s.ι s.condition)
    (fun s ↦ lift_comp_ι φ ψ s.ι s.condition)
    (fun s _m hm ↦ hom_ext φ ψ (hm.trans (lift_comp_ι φ ψ s.ι s.condition).symm))

end UniversalProperty

end Stacks.QuasicoherentAlgebraEqualizer

end
