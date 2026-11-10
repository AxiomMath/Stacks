module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# Descending a finite type quasi-coherent ideal along a cofiltered limit of schemes

Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms and let `X` be its limit.  A finite type quasi-coherent ideal of `𝒪_X` is the image of
the pullback of a finite type quasi-coherent ideal on one of the stages.

An ideal is presented here as a quasi-coherent module of finite type together with a
monomorphism into the structure sheaf.  The conclusion is an *epimorphic factorisation*: the
pulled-back ideal of the stage need not be isomorphic to the given ideal — pullback is only right
exact, so a monomorphism need not stay one — but it surjects onto it compatibly with the two
inclusions.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_ideal_pullback_epi_of_isLimit`: a finite type
  quasi-coherent ideal on the limit descends to a stage.

The companion statements of the same tag, for finite locally free modules and for invertible
modules, are
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso` and
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit`.

## Implementation notes

The argument runs on the quotient `𝒪_X / I` rather than on `I` itself, because the descent
results available are for modules of *finite presentation* and `𝒪_X / I` is one
(`Stacks.SheafOfModules.isFinitePresentation_cokernel`, Tag 0H96) while `I` need only be of
finite type.  Three stages are passed through, each produced by one clause of Tag 01ZR:

* a stage `i` where the quotient is the pullback of a module `Fᵢ` of finite presentation,
  by `exists_isFinitePresentation_pullback_iso_of_qcqs`;
* a stage `j` over `i` where the composite `𝒪_X ⟶ 𝒪_X / I ≅ (c.π.app i)^* Fᵢ` is the pullback of
  a morphism `θ`, by `exists_map_of_pullback_of_isLimit`;
* a stage `k` over `j` where `θ` has become an epimorphism.  Surjectivity is *not* descended
  directly: the cokernel of `θ` is of finite presentation, its pullback to the limit vanishes,
  so its identity and zero endomorphisms agree after pullback, and
  `exists_pullback_map_eq_of_isLimit'` makes them agree already at a stage, where the cokernel
  is therefore zero.

At the stage `k` the ideal is `ker θₖ`; it is quasi-coherent by
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` and of finite type by
`Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType` (Tag 01BP (2)).
The epimorphism onto `I` comes from `exists_epi_map_kernel_to_kernel`: pullback is additive and
right exact, so it carries the cokernel presentation of the epimorphism `θₖ` to a cokernel
presentation, hence the comparison from the pullback of `ker θₖ` to the kernel of the pulled-back
map is an epimorphism, and that kernel is `I`.

The identification of the pullback of the structure sheaf of a stage with the structure sheaf of
the limit is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, whose compatibility with a
factorisation `f ≫ g = h` of morphisms of schemes is
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq`.  That lemma is the only coherence
datum the argument needs about these identifications; `pullbackUnitIso_map_transport` below is
its combination with the naturality of the comparison isomorphisms.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v₁ u₁ v₂ u₂ v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### Kernels under an additive right exact functor -/

section Abelian

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- An additive functor carrying the cokernel presentation of an epimorphism `f` to a cokernel
presentation makes the comparison `F (ker f) ⟶ ker (F f)` an epimorphism.

In an abelian category an epimorphism is the cokernel of its kernel, so the image of that
cokernel diagram is a cokernel diagram, hence an exact short complex, and exactness of a short
complex whose last map is the given one is precisely surjectivity of the comparison. -/
private theorem epi_kernel_lift_map (F : C ⥤ D) [F.Additive] {A B : C} (f : A ⟶ B) [Epi f]
    [PreservesColimit (parallelPair (kernel.ι f) 0) F] :
    Epi (kernel.lift (F.map f) (F.map (kernel.ι f)) (by simp [← Functor.map_comp])) :=
  have h : IsColimit (CokernelCofork.ofπ f (kernel.condition f)) :=
    Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι f) (kernel.condition f))
      (kernelIsKernel f)
  (ShortComplex.exact_iff_epi_kernel_lift _).1
    ((ShortComplex.mk _ _
      (by simp [← Functor.map_comp] : F.map (kernel.ι f) ≫ F.map f = 0)).exact_of_g_is_cokernel
        (CokernelCofork.mapIsColimit _ h F))

/-- **The kernel of an epimorphism descends through an additive right exact functor.**  Let `F`
carry the cokernel presentation of an epimorphism `f : A ⟶ B` to a cokernel presentation, and let
`i : I ⟶ U` be a kernel of `q : U ⟶ Q` identified with `F f` through isomorphisms
`hu : F A ≅ U` and `hq : F B ≅ Q`.  Then `F (ker f)` surjects onto `I` compatibly with the two
inclusions.

The comparison `d : F (ker f) ⟶ I` exists because `i` is a kernel, and it is an epimorphism
because its composite with the monomorphism `ker (F f) ⟶ I` transported from `i` is the
epimorphism of `epi_kernel_lift_map`, which forces that monomorphism to be invertible. -/
private theorem exists_epi_map_kernel_to_kernel (F : C ⥤ D) [F.Additive] {A B : C} (f : A ⟶ B)
    [Epi f] [PreservesColimit (parallelPair (kernel.ι f) 0) F] {I U Q : D} (i : I ⟶ U) [Mono i]
    (q : U ⟶ Q) (hiq : i ≫ q = 0) (hu : F.obj A ≅ U) (hq : F.obj B ≅ Q)
    (hcompat : F.map f ≫ hq.hom = hu.hom ≫ q) (hi : IsLimit (KernelFork.ofι i hiq)) :
    ∃ d : F.obj (kernel f) ⟶ I, Epi d ∧ d ≫ i = F.map (kernel.ι f) ≫ hu.hom := by
  have hzero : (F.map (kernel.ι f) ≫ hu.hom) ≫ q = 0 := by
    rw [Category.assoc, ← hcompat, ← Category.assoc, ← Functor.map_comp, kernel.condition,
      F.map_zero, zero_comp]
  obtain ⟨d, hd⟩ : ∃ d : F.obj (kernel f) ⟶ I, d ≫ i = F.map (kernel.ι f) ≫ hu.hom :=
    ⟨hi.lift (KernelFork.ofι _ hzero), hi.fac _ WalkingParallelPair.zero⟩
  refine ⟨d, ?_, hd⟩
  have hzero' : (i ≫ hu.inv) ≫ F.map f = 0 := by
    rw [← cancel_mono hq.hom, Category.assoc, Category.assoc, hcompat, Iso.inv_hom_id_assoc,
      hiq, zero_comp]
  obtain ⟨g, hg⟩ : ∃ g : I ⟶ kernel (F.map f), g ≫ kernel.ι (F.map f) = i ≫ hu.inv :=
    ⟨kernel.lift _ _ hzero', kernel.lift_ι _ _ _⟩
  have hdg : d ≫ g =
      kernel.lift (F.map f) (F.map (kernel.ι f)) (by simp [← Functor.map_comp]) := by
    rw [← cancel_mono (kernel.ι (F.map f)), Category.assoc, hg, kernel.lift_ι, ← Category.assoc,
      hd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : Mono g := mono_of_mono_fac hg
  have : Epi (d ≫ g) := hdg ▸ epi_kernel_lift_map F f
  have : Epi g := epi_of_epi d g
  have : IsIso g := isIso_of_mono_of_epi g
  exact (epi_comp_iff_of_isIso d g).mp inferInstance

end Abelian

/-! ### Transporting a morphism out of the structure sheaf along a factorisation -/

/-- Naturality of the canonical identification of the pullback along a factorisation
`f ≫ g = h` of morphisms of schemes. -/
private theorem pullbackComp_congr_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (w : f ≫ g = h) {M N : Z.Modules} (m : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map m) ≫
        (Scheme.Modules.pullbackComp f g).hom.app N ≫
          (Scheme.Modules.pullbackCongr w).hom.app N =
      (Scheme.Modules.pullbackComp f g).hom.app M ≫
        (Scheme.Modules.pullbackCongr w).hom.app M ≫ (Scheme.Modules.pullback h).map m := by
  rw [show (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map m) =
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).map m from rfl,
    ← Category.assoc, (Scheme.Modules.pullbackComp f g).hom.naturality m, Category.assoc,
    (Scheme.Modules.pullbackCongr w).hom.naturality m]

/-- `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq` with the identifications moved to
the other side: the pullback along `f` of the inverse of `pullbackUnitIso g`, followed by the
canonical identification of the pullback along a factorisation `f ≫ g = h`, is the composite of
`pullbackUnitIso f` with the inverse of `pullbackUnitIso h`. -/
private theorem pullbackUnitIso_inv_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (w : f ≫ g = h) :
    (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullbackComp f g).hom.app (Scheme.unitModule Z) ≫
          (Scheme.Modules.pullbackCongr w).hom.app (Scheme.unitModule Z) =
      (Scheme.Modules.pullbackUnitIso f).hom ≫ (Scheme.Modules.pullbackUnitIso h).inv := by
  rw [← cancel_mono (Scheme.Modules.pullbackUnitIso h).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Scheme.Modules.pullbackUnitIso_comp_eq f g h w]
  simp

/-- The combination of `pullbackUnitIso_inv_comp` with `pullbackComp_congr_naturality`: a
morphism out of the structure sheaf of `Z`, pulled back along `g` and then along `f`, is the
morphism pulled back along `h` once the structure sheaves are identified. -/
private theorem pullbackUnitIso_map_transport {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (w : f ≫ g = h) {M : Z.Modules} (m : Scheme.unitModule Z ⟶ M) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackUnitIso g).inv ≫
          (Scheme.Modules.pullback g).map m) ≫
        (Scheme.Modules.pullbackComp f g).hom.app M ≫
          (Scheme.Modules.pullbackCongr w).hom.app M =
      (Scheme.Modules.pullbackUnitIso f).hom ≫
        (Scheme.Modules.pullbackUnitIso h).inv ≫ (Scheme.Modules.pullback h).map m := by
  rw [Functor.map_comp, Category.assoc, pullbackComp_congr_naturality f g w m,
    reassoc_of% pullbackUnitIso_inv_comp f g w]

/-- A morphism `ψ` out of the pullback along `g` of the structure sheaf whose pullback along `f`
is `φ` up to the canonical identifications, precomposed with `pullbackUnitIso g`, pulls back
along `f` to `φ` with the structure sheaves identified. -/
private theorem pullbackUnitIso_inv_comp_transport {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (w : f ≫ g = h) {F : Z.Modules}
    {φ : (Scheme.Modules.pullback h).obj (Scheme.unitModule Z) ⟶
      (Scheme.Modules.pullback h).obj F}
    {ψ : (Scheme.Modules.pullback g).obj (Scheme.unitModule Z) ⟶
      (Scheme.Modules.pullback g).obj F}
    (hψ : (Scheme.Modules.pullback f).map ψ ≫ (Scheme.Modules.pullbackComp f g).hom.app F ≫
        (Scheme.Modules.pullbackCongr w).hom.app F =
      (Scheme.Modules.pullbackComp f g).hom.app (Scheme.unitModule Z) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Scheme.unitModule Z) ≫ φ) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackUnitIso g).inv ≫ ψ) ≫
        (Scheme.Modules.pullbackComp f g).hom.app F ≫ (Scheme.Modules.pullbackCongr w).hom.app F =
      (Scheme.Modules.pullbackUnitIso f).hom ≫ (Scheme.Modules.pullbackUnitIso h).inv ≫ φ := by
  rw [Functor.map_comp, Category.assoc, hψ, reassoc_of% pullbackUnitIso_inv_comp f g w]

/-! ### Descent of a finite type quasi-coherent ideal -/

section Main

/- An ideal of `𝒪_X` is a morphism whose source is spelled `X.Modules` and whose target is
spelled `SheafOfModules X.ringCatSheaf`.  Those are two definitionally — but not reducibly —
equal spellings of one category, each with its own `Hom`, so instance search and `simp only`
both refuse to cross between them.  Making the two defining constants reducible is what lets
them. -/
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom

/-- `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` transported along two consecutive legs
of a cone of schemes, with the source of each leg spelled as the vertex of the cone.  This is
`pullbackUnitIso_map_transport` in the form the descent below needs; it is a separate
declaration because comparing the two sides is by far the costliest unification in that
proof. -/
private theorem pullbackUnitIso_map_transport_cone {J : Type u} [Category.{v} J]
    {D : J ⥤ Scheme.{u}} (c : Cone D) {j k : J} (d : k ⟶ j) {M : (D.obj j).Modules}
    (m : Scheme.unitModule (D.obj j) ⟶ M) :
    (Scheme.Modules.pullback (X := c.pt) (c.π.app k)).map
          ((Scheme.Modules.pullbackUnitIso (D.map d)).inv ≫
            (Scheme.Modules.pullback (D.map d)).map m) ≫
        ((Scheme.Modules.pullbackComp (X := c.pt) (c.π.app k) (D.map d)).app M ≪≫
          (Scheme.Modules.pullbackCongr (c.w d)).app M).hom =
      (Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app k)).hom ≫
        (Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app j)).inv ≫
          (Scheme.Modules.pullback (X := c.pt) (c.π.app j)).map m := by
  simp only [Iso.trans_hom, Iso.app_hom]
  exact pullbackUnitIso_map_transport (X := c.pt) (c.π.app k) (D.map d) (c.w d) m

/-- For a cofiltered diagram of schemes with affine transition morphisms, a morphism from a module
of finite type to a module of finite presentation on a quasi-compact stage whose pullback to the
limit is an epimorphism already has an epimorphic pullback to a later stage. -/
theorem exists_epi_pullback_map_of_isLimit {J : Type u} [Category.{v} J] [IsCofiltered J]
    {D : J ⥤ Scheme.{u}} [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D}
    (hc : IsLimit c) {j : J} [CompactSpace (D.obj j)] {M N : (D.obj j).Modules}
    [M.IsFiniteType] [N.IsFinitePresentation] (θ : M ⟶ N)
    [Epi ((Scheme.Modules.pullback (X := c.pt) (c.π.app j)).map θ)] :
    ∃ (k : J) (d : k ⟶ j), Epi ((Scheme.Modules.pullback (D.map d)).map θ) := by
  have : (cokernel θ).IsFinitePresentation :=
    _root_.Stacks.SheafOfModules.isFinitePresentation_cokernel θ
  -- A stage `k` over `j` at which `θ` has become an epimorphism: the cokernel of `θ` has
  -- vanishing pullback to the limit, so its identity and zero endomorphisms already agree at a
  -- stage, where the cokernel is therefore zero.
  obtain ⟨k, d, hdk⟩ :=
    exists_pullback_map_eq_of_isLimit' D c hc j (cokernel θ) (cokernel θ) (𝟙 _) 0
      (IsZero.eq_of_src (IsZero.of_iso (isZero_cokernel_of_epi _)
        (PreservesCokernel.iso (Scheme.Modules.pullback (X := c.pt) (c.π.app j)) θ)) _ _)
  exact ⟨k, d, Preadditive.epi_of_isZero_cokernel _ (IsZero.of_iso
    ((IsZero.iff_id_eq_zero _).2 (by simpa using hdk))
    (PreservesCokernel.iso (Scheme.Modules.pullback (D.map d)) θ).symm)⟩

variable {J : Type u} [Category.{v} J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
  [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)
  [∀ i : J, CompactSpace (D.obj i)] [∀ i : J, QuasiSeparatedSpace (D.obj i)]

/-- An epimorphism from the structure sheaf of the limit onto the pullback of a module `F` of
finite presentation on a stage `i` is, at some stage `k`, the pullback of an epimorphism from the
structure sheaf onto a module of finite presentation, compatibly with the identifications of the
structure sheaves. -/
theorem exists_epi_unit_pullback_of_isLimit (hc : IsLimit c) {i : J} (F : (D.obj i).Modules)
    [F.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (X := c.pt) (c.π.app i)).obj (Scheme.unitModule (D.obj i)) ⟶
      (Scheme.Modules.pullback (X := c.pt) (c.π.app i)).obj F) [Epi φ] :
    ∃ (k : J) (H : (D.obj k).Modules), H.IsFinitePresentation ∧
      ∃ θ : Scheme.unitModule (D.obj k) ⟶ H, Epi θ ∧
        ∃ β : (Scheme.Modules.pullback (X := c.pt) (c.π.app k)).obj H ≅
            (Scheme.Modules.pullback (X := c.pt) (c.π.app i)).obj F,
          (Scheme.Modules.pullback (X := c.pt) (c.π.app k)).map θ ≫ β.hom =
            (Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app k)).hom ≫
              (Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app i)).inv ≫ φ := by
  have : (Scheme.unitModule (D.obj i)).IsFinitePresentation :=
    isFinitePresentation_unit (D.obj i)
  obtain ⟨j, e, φj, hφj⟩ :=
    exists_map_of_pullback_of_isLimit D c hc i (Scheme.unitModule (D.obj i)) F φ
  let G : (D.obj j).Modules := (Scheme.Modules.pullback (D.map e)).obj F
  have : G.IsFinitePresentation := isFinitePresentation_pullback (D.map e) F
  have : (Scheme.unitModule (D.obj j)).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_unit (D.obj j)
  let θ : Scheme.unitModule (D.obj j) ⟶ G := (Scheme.Modules.pullbackUnitIso (D.map e)).inv ≫ φj
  let Uⱼ := Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app j)
  let Tⱼᵢ : (Scheme.Modules.pullback (X := c.pt) (c.π.app j)).obj G ≅
      (Scheme.Modules.pullback (X := c.pt) (c.π.app i)).obj F :=
    (Scheme.Modules.pullbackComp (X := c.pt) (c.π.app j) (D.map e)).app F ≪≫
      (Scheme.Modules.pullbackCongr (c.w e)).app F
  have hθ : (Scheme.Modules.pullback (X := c.pt) (c.π.app j)).map θ ≫ Tⱼᵢ.hom =
      Uⱼ.hom ≫ (Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app i)).inv ≫ φ := by
    simpa only [Tⱼᵢ, Iso.trans_hom, Iso.app_hom] using
      pullbackUnitIso_inv_comp_transport (X := c.pt) (c.π.app j) (D.map e) (c.w e) hφj
  have : Epi ((Scheme.Modules.pullback (X := c.pt) (c.π.app j)).map θ) := by
    have h : Epi ((Scheme.Modules.pullback (X := c.pt) (c.π.app j)).map θ ≫ Tⱼᵢ.hom) := by
      rw [hθ]
      infer_instance
    exact (epi_comp_iff_of_isIso _ _).mp h
  obtain ⟨k, d, _⟩ := exists_epi_pullback_map_of_isLimit hc θ
  let θₖ : Scheme.unitModule (D.obj k) ⟶ (Scheme.Modules.pullback (D.map d)).obj G :=
    (Scheme.Modules.pullbackUnitIso (D.map d)).inv ≫ (Scheme.Modules.pullback (D.map d)).map θ
  let Tₖⱼ : (Scheme.Modules.pullback (X := c.pt) (c.π.app k)).obj
        ((Scheme.Modules.pullback (D.map d)).obj G) ≅
      (Scheme.Modules.pullback (X := c.pt) (c.π.app j)).obj G :=
    (Scheme.Modules.pullbackComp (X := c.pt) (c.π.app k) (D.map d)).app G ≪≫
      (Scheme.Modules.pullbackCongr (c.w d)).app G
  have hdk : (Scheme.Modules.pullback (X := c.pt) (c.π.app k)).map θₖ ≫ Tₖⱼ.hom =
      (Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app k)).hom ≫ Uⱼ.inv ≫
        (Scheme.Modules.pullback (X := c.pt) (c.π.app j)).map θ :=
    pullbackUnitIso_map_transport_cone c d θ
  have : Epi θₖ := by
    dsimp only [θₖ]
    infer_instance
  refine ⟨k, _, isFinitePresentation_pullback (D.map d) G, θₖ, inferInstance, Tₖⱼ ≪≫ Tⱼᵢ, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, hdk, Category.assoc, Category.assoc, hθ,
    Iso.inv_hom_id_assoc]

include c in
/-- **Stacks Project, Tag 0B8W.**  A finite type quasi-coherent ideal of the structure sheaf of
the limit of a cofiltered system of quasi-compact and quasi-separated schemes with affine
transition morphisms is the image of the pullback of such an ideal at some stage.

An ideal is given as a quasi-coherent module `I` of finite type together with a monomorphism
`inclusion : I ⟶ 𝒪`.  The epimorphism `descend` of the conclusion is compatible with the two
inclusions; it need not be invertible, because the pullback of a monomorphism of modules need not
be one. -/
@[stacks 0B8W "finite_type_ideal_descent"]
theorem exists_ideal_pullback_epi_of_isLimit (hc : IsLimit c) (I : c.pt.Modules)
    [I.IsQuasicoherent] [I.IsFiniteType]
    (inclusion : I ⟶ SheafOfModules.unit c.pt.ringCatSheaf) [Mono inclusion] :
    ∃ i : J,
      letI : (SheafOfModules.pushforward
        (c.π.app i).toRingCatSheafHom).IsRightAdjoint :=
        Scheme.Modules.instIsRightAdjointPushforward (c.π.app i)
      ∃ Iᵢ : (D.obj i).Modules,
        Iᵢ.IsQuasicoherent ∧ Iᵢ.IsFiniteType ∧
          ∃ inclusionᵢ : Iᵢ ⟶ SheafOfModules.unit (D.obj i).ringCatSheaf,
            Mono inclusionᵢ ∧
              ∃ descend : (Scheme.Modules.pullback (c.π.app i)).obj Iᵢ ⟶ I,
                Epi descend ∧
                  descend ≫ inclusion =
                    (Scheme.Modules.pullback (c.π.app i)).map inclusionᵢ ≫
                      SheafOfModules.pullbackObjUnitToUnit
                        (c.π.app i).toRingCatSheafHom := by
  have : (SheafOfModules.unit c.pt.ringCatSheaf).IsFinitePresentation :=
    isFinitePresentation_unit c.pt
  have : (cokernel inclusion).IsFinitePresentation :=
    _root_.Stacks.SheafOfModules.isFinitePresentation_cokernel inclusion
  obtain ⟨i, Fᵢ, hFᵢ, ⟨eFᵢ⟩⟩ :=
    exists_isFinitePresentation_pullback_iso_of_qcqs D c hc (cokernel inclusion)
  have : Fᵢ.IsFinitePresentation := hFᵢ
  let Uᵢ : (Scheme.Modules.pullback (X := c.pt) (c.π.app i)).obj (Scheme.unitModule (D.obj i)) ≅
      SheafOfModules.unit c.pt.ringCatSheaf :=
    Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app i)
  let φ : (Scheme.Modules.pullback (X := c.pt) (c.π.app i)).obj (Scheme.unitModule (D.obj i)) ⟶
      (Scheme.Modules.pullback (X := c.pt) (c.π.app i)).obj Fᵢ :=
    Uᵢ.hom ≫ cokernel.π inclusion ≫ eFᵢ.hom
  have : Epi φ := by
    dsimp only [φ]
    infer_instance
  obtain ⟨k, Hₖ, _, θₖ, _, β, hβ⟩ := exists_epi_unit_pullback_of_isLimit D c hc Fᵢ φ
  have : Hₖ.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation Hₖ
  have : (Scheme.unitModule (D.obj k)).IsFinitePresentation :=
    isFinitePresentation_unit (D.obj k)
  have : (Scheme.unitModule (D.obj k)).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_unit (D.obj k)
  have hcompat : (Scheme.Modules.pullback (X := c.pt) (c.π.app k)).map θₖ ≫
      (β ≪≫ eFᵢ.symm).hom =
        (Scheme.Modules.pullbackUnitIso (X := c.pt) (c.π.app k)).hom ≫ cokernel.π inclusion := by
    rw [Iso.trans_hom, Iso.symm_hom, reassoc_of% hβ]
    dsimp only [φ, Uᵢ]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _)
  obtain ⟨descend, hdesc_epi, hdesc⟩ :=
    exists_epi_map_kernel_to_kernel (Scheme.Modules.pullback (X := c.pt) (c.π.app k)) θₖ inclusion
      (cokernel.π inclusion) (cokernel.condition inclusion) _ _ hcompat
      (Abelian.monoIsKernelOfCokernel
        (CokernelCofork.ofπ (cokernel.π inclusion) (cokernel.condition inclusion))
        (cokernelIsCokernel inclusion))
  exact ⟨k, kernel θₖ, QcohLimits.isQuasicoherent_kernel θₖ,
    _root_.Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType θₖ,
    kernel.ι θₖ, equalizer.ι_mono, descend, hdesc_epi, hdesc⟩

end Main

end Stacks.AlgebraicGeometry.ModuleLimits

end
