module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.Exactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSectionsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleKernelQuasicoherent

/-!
# The right adjoint `i^!` of the direct image along a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`, and let
`𝓘 = ker(i♯) ⊆ 𝒪_X` be the ideal cutting out `Z`.  Stacks 04CL asserts that the direct image
`i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` has a right adjoint `i^!`.

The source's construction is carried out here.  Given a quasi-coherent `𝒪_X`-module `𝓖`, let
`𝓗_Z(𝓖) ⊆ 𝓖` be the subsheaf of sections annihilated by `𝓘`, and let `𝓗_Z(𝓖)' ⊆ 𝓗_Z(𝓖)` be the
largest quasi-coherent `𝒪_X`-submodule inside it, which exists by Stacks 04CK.  Every map
`i_*𝓕 ⟶ 𝓖` from a direct image factors through `𝓗_Z(𝓖)`, because `𝓘` annihilates `i_*𝓕`, and
hence through `𝓗_Z(𝓖)'`, because `i_*𝓕` is quasi-coherent; the factorization is unique because
`𝓗_Z(𝓖)' ⟶ 𝓖` is a monomorphism.  So `𝓗_Z(𝓖)'` *corepresents* maps out of direct images, and
writing it as `i_*(i^!𝓖)` turns that into the adjunction.

That last step reads off part (3) of Stacks 04CJ: the essential-image assertion that a
quasi-coherent `𝒪_X`-module annihilated by `𝓘` is the direct image of a quasi-coherent
`𝒪_Z`-module, together with quasi-coherence of the direct image (Stacks 03M9 for the closed
immersion `i`).  The two are packaged as the data
`AlgebraicGeometry.Space.QuasicoherentDirectImageEquivalence`, and the declarations of this file
take them as that one argument, so that the construction can be read off at any morphism for
which they hold.  For a closed immersion they hold:
`AlgebraicGeometry.Space.quasicoherentDirectImageEquivalence` produces them, and
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQuasicoherentUpperShriek.lean` is where
Stacks 04CL is stated and registered.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentDirectImageEquivalence`: part (3) of Stacks 04CJ in the
  form consumed here — the direct image carries quasi-coherent modules to quasi-coherent modules,
  and every quasi-coherent module annihilated by `𝓘` is a direct image of one.  It is proved for
  a closed immersion in
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQuasicoherentEquivalence.lean`.
* `AlgebraicGeometry.Space.quasicoherentPushforwardOfEquivalence`: `i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.quasicoherentRightAdjoint`: the functor `i^!` of Stacks 04CL, and
  `AlgebraicGeometry.Space.quasicoherentPushforwardAdjunction` the adjunction `i_* ⊣ i^!`.

## Main results

* `AlgebraicGeometry.Space.exists_largest_annihilated_quasicoherentSubobject`: **with no
  hypothesis**, a quasi-coherent `𝒪_X`-module `𝓖` has a largest quasi-coherent submodule
  annihilated by `𝓘`, and every quasi-coherent annihilated module maps into it compatibly with
  the maps to `𝓖`.  This is the content of Stacks 04CK used by Stacks 04CL.
* `AlgebraicGeometry.Space.fullyFaithfulQuasicoherentPushforward`: `i_*` is fully faithful on
  quasi-coherent modules, the target now being `QCoh(𝒪_X)` rather than the annihilated modules of
  `AlgebraicGeometry.Space.fullyFaithfulQuasicoherentModulePushforward`.
* `AlgebraicGeometry.Space.isLeftAdjoint_quasicoherentPushforward`: the existence of the right
  adjoint, read off the part-(3) data of Stacks 04CJ.  Stacks 04CL is this at the data a closed
  immersion produces, and is registered on
  `AlgebraicGeometry.Space.isLeftAdjoint_quasicoherentDirectImage`.

## Implementation notes

The annihilator subsheaf is `Stacks.SheafOfModules.annihilatorSubmodule` at the kernel ideal
`SheafOfModules.kerIdeal (AlgebraicGeometry.Space.structureSharp B S hS f)`, which is the same
ideal as the one `AlgebraicGeometry.Space.AnnihilatedByKerIdeal` is stated with, so the
factorization lemma `Stacks.SheafOfModules.annihilatorLift` applies to a direct image on the nose
through `AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`.  Its commutativity
hypothesis is discharged by
`AlgebraicGeometry.Space.ringSheaf_mul_comm_smallEtaleRingedSite`: the structure
sheaf of the small étale ringed site is a sheaf of commutative rings, and
`AlgebraicGeometry.Space.structureRingSheaf` only forgets that.

Stacks 04CK is formalized as a statement about `CategoryTheory.Subobject`, while the annihilator is a
`SheafOfModules.Submodule`; the two are joined by `CategoryTheory.Subobject.mk` of the inclusion
and `CategoryTheory.Subobject.underlyingIso`, and
`AlgebraicGeometry.Space.exists_largest_annihilated_quasicoherentSubobject` is stated with a plain
monomorphism so that no consumer has to cross that bridge again.

The adjunction is produced by `CategoryTheory.isLeftAdjoint_iff_hasTerminal_costructuredArrow`
rather than built by hand, exactly as in
`Stacks.SheafOfModules.isLeftAdjoint_of_essImage_eq_annihilated`: the terminal object of
`CostructuredArrow i_* 𝓖` is the quasi-coherent `𝒪_Z`-module that the part-(3) data produces from
the largest annihilated quasi-coherent submodule of `𝓖`.

## References

* [Stacks Project, Lemma 67.14.3 (Tag 04CL)](https://stacks.math.columbia.edu/tag/04CL)
* [Stacks Project, Tag 04CK](https://stacks.math.columbia.edu/tag/04CK)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Lemma 17.6.3 (Tag 01AZ)](https://stacks.math.columbia.edu/tag/01AZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sections of the structure sheaf of an algebraic space commute.  The sheaf of rings
`AlgebraicGeometry.Space.structureRingSheaf` in which the `𝒪`-modules are indexed is the
structure sheaf of the small étale ringed site with its commutativity forgotten, so this is
`mul_comm` of the sections of the latter. -/
theorem ringSheaf_mul_comm_smallEtaleRingedSite (Z : AlgebraicSpaces B S hS)
    (U : (smallEtaleRingedSite B S hS Z.1 Z.2).Cᵒᵖ)
    (a b : (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj.obj U) :
    a * b = b * a :=
  mul_comm (G := ToType ((smallEtaleRingedSite B S hS Z.1 Z.2).O.obj.obj U)) a b

variable {X Y : AlgebraicSpaces B S hS}

/-- **The largest quasi-coherent submodule annihilated by the ideal cutting out a closed
subspace**, with no hypothesis.  Let `f : X ⟶ Y` be a morphism of algebraic spaces, let
`𝓘 = ker(f♯)` and let `𝓖` be a quasi-coherent `𝒪_Y`-module.  There is a quasi-coherent
`𝒪_Y`-submodule `𝓟 ⊆ 𝓖` annihilated by `𝓘` through which every morphism into `𝓖` from a
quasi-coherent `𝒪_Y`-module annihilated by `𝓘` factors.

The subsheaf of sections of `𝓖` annihilated by `𝓘` is
`Stacks.SheafOfModules.annihilatorSubmodule`, and `𝓟` is its largest quasi-coherent submodule,
which exists by Stacks 04CK (`existsUnique_largestQuasicoherentSubobject`).  The factorization is
`Stacks.SheafOfModules.annihilatorLift` followed by the bijection of Stacks 04CK, and `𝓟` is
annihilated because it injects into the annihilator subsheaf. -/
theorem exists_largest_annihilated_quasicoherentSubobject (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) [G.IsQuasicoherentOnSite] :
    ∃ (P : Modules.{u, u} B S hS Y.1 Y.2) (_ : P.IsQuasicoherentOnSite) (j : P ⟶ G) (_ : Mono j),
      AnnihilatedByKerIdeal B S hS f P ∧
        ∀ (H : Modules.{u, u} B S hS Y.1 Y.2), H.IsQuasicoherentOnSite →
          AnnihilatedByKerIdeal B S hS f H → ∀ φ : H ⟶ G, ∃ ψ : H ⟶ P, ψ ≫ j = φ := by
  classical
  set I := SheafOfModules.kerIdeal (structureSharp B S hS f) with hI
  set A := Stacks.SheafOfModules.annihilatorSubmodule G
    (ringSheaf_mul_comm_smallEtaleRingedSite B S hS Y) I with hA
  obtain ⟨⟨q, hqc⟩, hbij, -⟩ :=
    existsUnique_largestQuasicoherentSubobject B S hS Y.1 Y.2 G (Subobject.mk A.ι)
  refine ⟨(q : Modules.{u, u} B S hS Y.1 Y.2), hqc,
    q.arrow ≫ (Subobject.mk A.ι).arrow, inferInstance, ?_, ?_⟩
  · intro U a ha m
    refine injective_val_app_of_mono B S hS (q.arrow ≫ (Subobject.underlyingIso A.ι).hom) U ?_
    exact (((q.arrow ≫ (Subobject.underlyingIso A.ι).hom).val.app U).hom.map_smul a m).trans
      ((Stacks.SheafOfModules.smul_annihilatorSubmodule_eq_zero G
        (ringSheaf_mul_comm_smallEtaleRingedSite B S hS Y) I U a ha
        ((q.arrow ≫ (Subobject.underlyingIso A.ι).hom).val.app U m)).trans (map_zero _).symm)
  · intro H hH hHann φ
    obtain ⟨ψ, hψ⟩ := (hbij H).surjective (Stacks.SheafOfModules.annihilatorLift G
      (ringSheaf_mul_comm_smallEtaleRingedSite B S hS Y) I hHann φ ≫
        (Subobject.underlyingIso A.ι).inv)
    refine ⟨ψ, ?_⟩
    rw [← Category.assoc, show ψ ≫ q.arrow = _ from hψ, Category.assoc,
      ← Subobject.underlyingIso_hom_comp_eq_mk A.ι, Iso.inv_hom_id_assoc]
    exact Stacks.SheafOfModules.annihilatorLift_comp_ι G _ I hHann φ

/-! ### Part (3) of Stacks 04CJ, as the data the construction reads off -/

/-- **Part (3) of Stacks 04CJ, in the form consumed by Stacks 04CL.**  For a closed immersion
`f : X ⟶ Y` of algebraic spaces the direct image is an equivalence from the quasi-coherent
`𝒪_X`-modules onto the quasi-coherent `𝒪_Y`-modules annihilated by `𝓘 = ker(f♯)`.  Its full
faithfulness is `AlgebraicGeometry.Space.fullyFaithfulModulePushforward` and the annihilation of a
direct image is `AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`; the two clauses
below are the rest, and they hold for a closed immersion by
`AlgebraicGeometry.Space.quasicoherentDirectImageEquivalence`. -/
structure QuasicoherentDirectImageEquivalence (f : X ⟶ Y) : Prop where
  /-- The direct image of a quasi-coherent `𝒪_X`-module is quasi-coherent.  This is Stacks 03M9
  for the closed immersion `f`. -/
  pushforward_isQuasicoherentOnSite : ∀ F : Modules.{u, u} B S hS X.1 X.2,
    F.IsQuasicoherentOnSite → ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite
  /-- A quasi-coherent `𝒪_Y`-module annihilated by `𝓘` is the direct image of a quasi-coherent
  `𝒪_X`-module.  This is the essential-image assertion of Stacks 04CJ, part (3). -/
  exists_pushforward_iso : ∀ G : Modules.{u, u} B S hS Y.1 Y.2, G.IsQuasicoherentOnSite →
    AnnihilatedByKerIdeal B S hS f G → ∃ F : Modules.{u, u} B S hS X.1 X.2,
      F.IsQuasicoherentOnSite ∧ Nonempty ((modulePushforward B S hS f).obj F ≅ G)

/-! ### Direct image on quasi-coherent modules, and its right adjoint -/

/-- Direct image as a functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`, the lift of
`AlgebraicGeometry.Space.modulePushforward` along the first clause of
`AlgebraicGeometry.Space.QuasicoherentDirectImageEquivalence`. -/
def quasicoherentPushforwardOfEquivalence (f : X ⟶ Y)
    (h : QuasicoherentDirectImageEquivalence B S hS f) :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).lift
    (ObjectProperty.ι _ ⋙ modulePushforward B S hS f)
    fun M ↦ h.pushforward_isQuasicoherentOnSite M.obj M.property

/-- Composing `AlgebraicGeometry.Space.quasicoherentPushforwardOfEquivalence` with the
inclusion of the quasi-coherent modules is direct image.  This holds by definition: the
functor *is* that lift. -/
def quasicoherentPushforwardCompIso (f : X ⟶ Y)
    (h : QuasicoherentDirectImageEquivalence B S hS f) :
    quasicoherentPushforwardOfEquivalence B S hS f h ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) ≅
      ObjectProperty.ι _ ⋙ modulePushforward B S hS f :=
  Iso.refl _

/-- Direct image along a closed immersion is fully faithful as a functor
`QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`.  It is fully faithful on all modules by
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`, and a full subcategory inclusion is
fully faithful. -/
def fullyFaithfulQuasicoherentPushforward (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (h : QuasicoherentDirectImageEquivalence B S hS f) :
    (quasicoherentPushforwardOfEquivalence B S hS f h).FullyFaithful :=
  have := (fullyFaithfulModulePushforward B S hS f hf).full
  have := (fullyFaithfulModulePushforward B S hS f hf).faithful
  have : (quasicoherentPushforwardOfEquivalence B S hS f h).Faithful :=
    Functor.Faithful.of_comp_iso (quasicoherentPushforwardCompIso B S hS f h)
  have : (quasicoherentPushforwardOfEquivalence B S hS f h).Full :=
    Functor.Full.of_comp_faithful_iso (quasicoherentPushforwardCompIso B S hS f h)
  Functor.FullyFaithful.ofFullyFaithful _

/-- **The construction of the right adjoint of Stacks 04CL, at the part-(3) data of
Stacks 04CJ.**  For a closed immersion `f : X ⟶ Y` of algebraic spaces whose direct image is
described by `h` as in part (3), the direct image `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` has a right
adjoint, the functor `f^!` of the source.  Stacks 04CL is this at the data a closed immersion
produces, namely `AlgebraicGeometry.Space.isLeftAdjoint_quasicoherentDirectImage`.

For a quasi-coherent `𝒪_Y`-module `𝓖` the terminal object of `CostructuredArrow f_* 𝓖` is the
quasi-coherent `𝒪_X`-module whose direct image is the largest quasi-coherent submodule of `𝓖`
annihilated by the ideal cutting out `X`
(`AlgebraicGeometry.Space.exists_largest_annihilated_quasicoherentSubobject`, which is
Stacks 04CK): every map `f_*𝓕 ⟶ 𝓖` factors through it uniquely, the factorization existing because
`f_*𝓕` is quasi-coherent and annihilated and being unique because the inclusion into `𝓖` is a
monomorphism, and the factorization is transported to `𝓕 ⟶ f^!𝓖` by full faithfulness of `f_*`. -/
theorem isLeftAdjoint_quasicoherentPushforward (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (h : QuasicoherentDirectImageEquivalence B S hS f) :
    (quasicoherentPushforwardOfEquivalence B S hS f h).IsLeftAdjoint := by
  classical
  let Φ := quasicoherentPushforwardOfEquivalence B S hS f h
  let ff := fullyFaithfulQuasicoherentPushforward B S hS f hf h
  rw [isLeftAdjoint_iff_hasTerminal_costructuredArrow]
  intro G
  obtain ⟨P, hPq, j, hjm, hPann, hfac⟩ :=
    exists_largest_annihilated_quasicoherentSubobject B S hS f G.obj
  obtain ⟨F₀, hF₀, ⟨ε⟩⟩ := h.exists_pushforward_iso P hPq hPann
  let τ : Φ.obj ⟨F₀, hF₀⟩ ⟶ G := ObjectProperty.homMk (ε.hom ≫ j)
  have hτ : Mono τ :=
    ⟨fun g₁ g₂ hg ↦ ObjectProperty.hom_ext _ ((cancel_mono (ε.hom ≫ j)).mp (congrArg (·.hom) hg))⟩
  let t : CostructuredArrow Φ G := CostructuredArrow.mk τ
  let lift (c : CostructuredArrow Φ G) : c ⟶ t := by
    have hex := hfac ((modulePushforward B S hS f).obj c.left.obj)
      (h.pushforward_isQuasicoherentOnSite c.left.obj c.left.property)
      (annihilatedByKerIdeal_modulePushforward B S hS f c.left.obj) c.hom.hom
    refine CostructuredArrow.homMk
      (ff.preimage (ObjectProperty.homMk (hex.choose ≫ ε.inv))) ?_
    dsimp only [t, CostructuredArrow.mk_right, CostructuredArrow.mk_hom_eq_self]
    rw [ff.map_preimage]
    refine ObjectProperty.hom_ext _ ?_
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, τ]
    exact (Category.assoc _ _ _).trans
      ((congrArg (hex.choose ≫ ·) (Iso.inv_hom_id_assoc ε j)).trans hex.choose_spec)
  refine (IsTerminal.ofUniqueHom lift ?_).hasTerminal
  intro c φ
  refine CostructuredArrow.hom_ext _ _ (ff.map_injective ?_)
  refine (cancel_mono τ).mp ?_
  exact φ.w.trans (lift c).w.symm

/-- The functor `f^!` of the source at the part-(3) data of Stacks 04CJ: the right adjoint of the
direct image `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` along a closed immersion.  For a closed immersion
this is `AlgebraicGeometry.Space.quasicoherentRightAdjointOfClosedImmersion`, which carries the
Stacks 04CL registration. -/
def quasicoherentRightAdjoint (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (h : QuasicoherentDirectImageEquivalence B S hS f) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2 :=
  have := isLeftAdjoint_quasicoherentPushforward B S hS f hf h
  (quasicoherentPushforwardOfEquivalence B S hS f h).rightAdjoint

/-- The adjunction `f_* ⊣ f^!` exhibiting `AlgebraicGeometry.Space.quasicoherentRightAdjoint` as
a right adjoint of the direct image of quasi-coherent modules along a closed immersion of
algebraic spaces, at the part-(3) data of Stacks 04CJ.  For a closed immersion this is
`AlgebraicGeometry.Space.quasicoherentDirectImageAdjunction`, which carries the Stacks 04CL
registration. -/
def quasicoherentPushforwardAdjunction (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (h : QuasicoherentDirectImageEquivalence B S hS f) :
    quasicoherentPushforwardOfEquivalence B S hS f h ⊣ quasicoherentRightAdjoint B S hS f hf h :=
  have := isLeftAdjoint_quasicoherentPushforward B S hS f hf h
  Adjunction.ofIsLeftAdjoint (quasicoherentPushforwardOfEquivalence B S hS f h)

end AlgebraicGeometry.Space

end
