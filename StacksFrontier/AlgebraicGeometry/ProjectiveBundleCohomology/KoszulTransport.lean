module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoDerived
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.PullbackWedge
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.KoszulCohomology
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.ProjMapCard.RestrictionComparison

/-!
# The Koszul filtration of a projective bundle under an isomorphism of bundles

Let `π : 𝐏(E) ⟶ S` and `π' : 𝐏(E') ⟶ S` be the projective bundles of quasi-coherent
`𝒪_S`-modules, with twists, and `f : 𝐏(E') ⟶ 𝐏(E)` an isomorphism over `S` along which the
twists, their multiplication and the tautological surjections `π^* E ⟶ 𝒪(1)` correspond. Then
pulling back along `f` carries the Koszul filtration of `𝐏(E)` to that of `𝐏(E')`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.pullbackPullbackIso`:
  `f^* p^* M ≅ p'^* M` for `f ≫ p = p'`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.kernelIsoOfIso`: an exact functor carries
  a kernel to the kernel of an isomorphic arrow.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open scoped TensorProduct

open Stacks.AlgebraicGeometry.LerayAffineBase (pushDelta)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Generic

variable {X X' T : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ T) (p' : X' ⟶ T) (hbase : f ≫ p = p')

/-- The pullback unit of a morphism of schemes, on a section. -/
public abbrev pbUnit {Y Z : Scheme.{u}} (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens)
    (s : M.val.obj (op U)) : ((Scheme.Modules.pullback g).obj M).val.obj (op (g ⁻¹ᵁ U)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op U) s

/-- **Morphisms out of an iterated pullback `f^* p^* M` are determined on iterated pullback units
of sections of `M`.** -/
public theorem pullback_pullback_hom_ext {M : T.Modules} {N : X'.Modules}
    {θ₁ θ₂ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj M) ⟶ N}
    (h : ∀ (U : T.Opens) (s : M.val.obj (op U)),
      θ₁.val.app (op (f ⁻¹ᵁ (p ⁻¹ᵁ U))) (pbUnit f _ _ (pbUnit p M U s)) =
        θ₂.val.app (op (f ⁻¹ᵁ (p ⁻¹ᵁ U))) (pbUnit f _ _ (pbUnit p M U s))) :
    θ₁ = θ₂ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  ext U s
  simp only [Adjunction.homEquiv_unit]
  exact h U s

/-- `f^* p^* M ≅ p'^* M` for `f ≫ p = p'`. -/
public def pullbackPullbackIso (M : T.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback p').obj M :=
  (Scheme.Modules.pullbackComp f p).app M ≪≫ (Scheme.Modules.pullbackCongr hbase).app M

/-- The comparison `f^* p^* M ⟶ (f ≫ p)^* M` sends iterated pullback units to the pullback unit. -/
private theorem pullbackComp_hom_pbUnit (M : T.Modules) (U : T.Opens) (s : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp f p).hom.app M).val.app (op ((f ≫ p) ⁻¹ᵁ U))
      (pbUnit f _ _ (pbUnit p M U s)) = pbUnit (f ≫ p) M U s :=
  (congrArg (((Scheme.Modules.pullbackComp f p).hom.app M).val.app (op ((f ≫ p) ⁻¹ᵁ U)))
      (Scheme.Modules.pullbackComp_inv_unit f p M U s).symm).trans
    (Stacks.SheafOfModules.hom_val_app_inv_val_app ((Scheme.Modules.pullbackComp f p).app M) _ _)

/-- The restriction map along `(f ≫ p) ⁻¹ᵁ U = f ⁻¹ᵁ (p ⁻¹ᵁ U)` is the identity. -/
private theorem presheaf_map_comp_preimage (N : X'.Modules) (U : T.Opens) :
    N.val.presheaf.map (homOfLE (le_of_eq (by rw [Scheme.Hom.comp_preimage] :
      (f ≫ p) ⁻¹ᵁ U = f ⁻¹ᵁ (p ⁻¹ᵁ U)))).op = 𝟙 _ := by
  rw [show homOfLE (le_of_eq (by rw [Scheme.Hom.comp_preimage] :
    (f ≫ p) ⁻¹ᵁ U = f ⁻¹ᵁ (p ⁻¹ᵁ U))) = 𝟙 _ from Subsingleton.elim _ _]
  exact N.val.presheaf.map_id _

/-- Along `rfl`, the comparison of direct images of `pushforwardCongr` is the identity. -/
private theorem pushforwardCongr_rfl_app_app (N : X'.Modules) (U : T.Opens) :
    ((Scheme.Modules.pushforwardCongr (rfl : f ≫ p = f ≫ p)).hom.app N).app U = 𝟙 _ := by
  rw [Scheme.Modules.pushforwardCongr_hom_app_app]
  exact N.presheaf.map_id _

/-- **The pullback of an adjoint transpose.** For `h : M ⟶ p_* N` and `h' : M ⟶ p'_* N'`
compatible with `θ : f^* N ≅ N'`, the pullback along `f` of the transpose of `h` is the transpose
of `h'`, under `f^* p^* M ≅ p'^* M`. -/
public theorem pullback_homEquiv_symm {M : T.Modules} {N : X.Modules} {N' : X'.Modules}
    (θ : (Scheme.Modules.pullback f).obj N ⟶ N') (h : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (h' : M ⟶ (Scheme.Modules.pushforward p').obj N')
    (hh : ∀ (U : T.Opens) (s : M.val.obj (op U)),
      N'.val.presheaf.map (homOfLE (le_of_eq (by rw [← hbase, Scheme.Hom.comp_preimage] :
          p' ⁻¹ᵁ U = f ⁻¹ᵁ (p ⁻¹ᵁ U)))).op
          (θ.val.app (op (f ⁻¹ᵁ (p ⁻¹ᵁ U))) (pbUnit f N _ (h.val.app (op U) s))) =
        h'.val.app (op U) s) :
    (Scheme.Modules.pullback f).map
        (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm h) ≫ θ =
      (pullbackPullbackIso f p p' hbase M).hom ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction p').homEquiv _ _).symm h' := by
  subst hbase
  refine pullback_pullback_hom_ext f p fun U s => ?_
  have ht : ∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z) {A : Z.Modules} {B : Y.Modules}
      (k : A ⟶ (Scheme.Modules.pushforward g).obj B) (V : Z.Opens) (a : A.val.obj (op V)),
      (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm k).val.app
        (op (g ⁻¹ᵁ V)) (pbUnit g A V a) = k.val.app (op V) a := by
    intro Y Z g A B k V a
    have := congrArg (fun φ => φ.val.app (op V) a)
      (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv A B).apply_symm_apply k)
    simp only [Adjunction.homEquiv_unit] at this
    exact this
  have hc' := pullbackComp_hom_pbUnit f p M U s
  have hn : ((Scheme.Modules.pullback f).map
      (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm h)).val.app
        (op (f ⁻¹ᵁ (p ⁻¹ᵁ U))) (pbUnit f _ _ (pbUnit p M U s)) =
      pbUnit f N _ ((((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm h).val.app
        (op (p ⁻¹ᵁ U)) (pbUnit p M U s)) :=
    (congrArg (fun φ => φ.val.app (op (p ⁻¹ᵁ U)) (pbUnit p M U s))
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality
        (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm h))).symm
  have h1 := hh U s
  rw [presheaf_map_comp_preimage f p N' U] at h1
  refine Eq.trans (congrArg (θ.val.app _) (hn.trans (congrArg (pbUnit f N _) (ht p h U s)))) ?_
  refine Eq.trans h1 ?_
  refine Eq.trans (ht (f ≫ p) h' U s).symm ?_
  exact congrArg ((((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ p)).homEquiv M N').symm
    h').val.app _) hc'.symm

/-- Reassociating a transpose along a morphism of its source. -/
public theorem comp_homEquiv_symm_comp {P : X'.Modules} {M M' : T.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pullback p').obj M) (c : M ⟶ M')
    (g : M' ⟶ (Scheme.Modules.pushforward p').obj N) :
    a ≫ ((Scheme.Modules.pullbackPushforwardAdjunction p').homEquiv M N).symm (c ≫ g) =
      a ≫ (Scheme.Modules.pullback p').map c ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction p').homEquiv M' N).symm g := by
  rw [Adjunction.homEquiv_naturality_left_symm]

/-- Two restriction maps of a sheaf of modules compose to one. -/
public theorem presheaf_map_map {Y : Scheme.{u}} (M : Y.Modules) {U V W : Y.Opens} (h₁ : V ≤ U)
    (h₂ : W ≤ V) (h₃ : W ≤ U) (x : M.val.obj (op U)) :
    M.val.presheaf.map (homOfLE h₂).op (M.val.presheaf.map (homOfLE h₁).op x) =
      M.val.presheaf.map (homOfLE h₃).op x :=
  ConcreteCategory.congr_hom
    (presheaf_map_comp₂ M.val.presheaf (homOfLE h₁).op (homOfLE h₂).op (homOfLE h₃).op) x

/-- Restriction of sections along the image of an inverse image: `p_* N ⟶ p'_*(N|_{X'})` for an
open immersion `f` with `f ≫ p = p'`. -/
public def pushforwardRestrictMap [IsOpenImmersion f] (N : X.Modules) :
    (Scheme.Modules.pushforward p).obj N ⟶
      (Scheme.Modules.pushforward p').obj (Scheme.Modules.restrict N f) :=
  (Scheme.Modules.pushforward p).map ((Scheme.Modules.restrictAdjunction f).unit.app N) ≫
    (Scheme.Modules.pushforwardComp f p).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr hbase).hom.app _

/-- The pullback of a section, transported along an open immersion and a morphism out of the
restriction, compared with a map into the direct image. -/
public theorem pullbackUnit_restrict_comp [IsOpenImmersion f] {M : T.Modules} {N : X.Modules}
    {N' : X'.Modules} (φ : Scheme.Modules.restrict N f ⟶ N')
    (h : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (h' : M ⟶ (Scheme.Modules.pushforward p').obj N')
    (hψ : h ≫ pushforwardRestrictMap f p p' hbase N ≫ (Scheme.Modules.pushforward p').map φ = h')
    (U : T.Opens) (s : M.val.obj (op U)) :
    N'.val.presheaf.map (homOfLE (le_of_eq (by rw [← hbase, Scheme.Hom.comp_preimage] :
          p' ⁻¹ᵁ U = f ⁻¹ᵁ (p ⁻¹ᵁ U)))).op
        ((((Scheme.Modules.restrictFunctorIsoPullback f).app N).inv ≫ φ).val.app
          (op (f ⁻¹ᵁ (p ⁻¹ᵁ U))) (pbUnit f N _ (h.val.app (op U) s))) =
      h'.val.app (op U) s := by
  subst hψ hbase
  have hρ := Stacks.AlgebraicGeometry.ProjMapCard.pullbackUnit_eq_restrictFunctorIsoPullback f N
    (p ⁻¹ᵁ U) (h.val.app (op U) s)
  have h1 : (((Scheme.Modules.restrictFunctorIsoPullback f).app N).inv ≫ φ).val.app
      (op (f ⁻¹ᵁ (p ⁻¹ᵁ U))) (pbUnit f N _ (h.val.app (op U) s)) =
      φ.val.app _ (N.val.presheaf.map (homOfLE (f.image_preimage_le (p ⁻¹ᵁ U))).op
        (h.val.app (op U) s)) :=
    congrArg (φ.val.app _) ((congrArg (((Scheme.Modules.restrictFunctorIsoPullback f).app
      N).inv.val.app _) hρ).trans (Stacks.SheafOfModules.inv_val_app_hom_val_app
        ((Scheme.Modules.restrictFunctorIsoPullback f).app N) _ _))
  rw [h1]
  rw [presheaf_map_comp_preimage f p N' U]
  refine (ConcreteCategory.id_apply _).trans ?_
  refine congrArg (φ.val.app _) ?_
  exact (ConcreteCategory.congr_hom
    (pushforwardCongr_rfl_app_app f p (Scheme.Modules.restrict N f) U)
    (N.val.presheaf.map (homOfLE (f.image_preimage_le (p ⁻¹ᵁ U))).op (h.val.app (op U) s))).symm

/-- `(a ≪≫ G.mapIso c).hom ≫ t = a.hom ≫ G.map c.hom ≫ t`. -/
public theorem trans_mapIso_hom_comp {Y Z : Scheme.{u}} {P R : Y.Modules}
    (G : Z.Modules ⥤ Y.Modules) {M M' : Z.Modules} (a : P ≅ G.obj M) (c : M ≅ M')
    (t : G.obj M' ⟶ R) :
    (a ≪≫ G.mapIso c).hom ≫ t = a.hom ≫ G.map c.hom ≫ t := by
  simp

/-- An exact functor carries the kernel of `u` to the kernel of any `u'` isomorphic to `G u`. -/
public def kernelIsoOfIso {Y Z : Scheme.{u}} (G : Z.Modules ⥤ Y.Modules)
    [PreservesFiniteLimits G] {A B : Z.Modules} {A' B' : Y.Modules} (u : A ⟶ B) (u' : A' ⟶ B')
    (a : G.obj A ≅ A') (b : G.obj B ≅ B') (w : G.map u ≫ b.hom = a.hom ≫ u') :
    G.obj (kernel u) ≅ kernel u' :=
  PreservesKernel.iso G u ≪≫ kernel.mapIso _ _ a b w

/-- `kernelIsoOfIso` is compatible with the inclusions. -/
public theorem kernelIsoOfIso_ι {Y Z : Scheme.{u}} (G : Z.Modules ⥤ Y.Modules)
    [PreservesFiniteLimits G] {A B : Z.Modules} {A' B' : Y.Modules} (u : A ⟶ B) (u' : A' ⟶ B')
    (a : G.obj A ≅ A') (b : G.obj B ≅ B') (w : G.map u ≫ b.hom = a.hom ≫ u') :
    G.map (kernel.ι u) ≫ a.hom = (kernelIsoOfIso G u u' a b w).hom ≫ kernel.ι u' := by
  simp [kernelIsoOfIso, kernel.map]

/-- `f^* p^* M ≅ (f ≫ p)^* M` on an iterated pullback unit. -/
public theorem pullbackPullbackIso_rfl_pbUnit (M : T.Modules) (U : T.Opens)
    (s : M.val.obj (op U)) :
    (pullbackPullbackIso f p (f ≫ p) rfl M).hom.val.app (op ((f ≫ p) ⁻¹ᵁ U))
        (pbUnit f _ _ (pbUnit p M U s)) = pbUnit (f ≫ p) M U s := by
  exact pullbackComp_hom_pbUnit f p M U s

end Generic

/-- In a commutative square whose vertical sides are isomorphisms, the square of inverses
commutes. -/
public theorem iso_square_inv {C : Type*} [Category C] {a b c d : C} (A : a ≅ b) (B : c ≅ d)
    (x : a ⟶ c) (y : b ⟶ d) (h : A.hom ≫ y = x ≫ B.hom) : A.inv ≫ x = y ≫ B.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `tensorPullbackIso` is natural in the first factor, for the tensor functor of a scheme. -/
public theorem tensorPullbackIso_naturality' {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' : Y.Modules}
    {N N' L' : X.Modules} {L : Y.Modules} (a : (Scheme.Modules.pullback f).obj M ≅ N)
    (a' : (Scheme.Modules.pullback f).obj M' ≅ N') (l : (Scheme.Modules.pullback f).obj L ≅ L')
    (g : M ⟶ M') (g' : N ⟶ N')
    (hg : (Scheme.Modules.pullback f).map g ≫ a'.hom = a.hom ≫ g') :
    (Scheme.Modules.pullback f).map ((Stacks.ProjectionFormula.tensorRightInvertible Y L).map g) ≫
        (tensorPullbackIso f.toLRSHom.toShHom a' l).hom =
      (tensorPullbackIso f.toLRSHom.toShHom a l).hom ≫
        (Stacks.ProjectionFormula.tensorRightInvertible X L').map g' :=
  tensorPullbackIso_naturality f.toLRSHom.toShHom a a' l g g' hg

/-- **A short complex tensored with `L`, under pullback.** Isomorphisms `f^* T_i ≅ T'_i`
compatible with the arrows and `f^* L ≅ L'` give `f^*(T ⊗ L) ≅ T' ⊗ L'`. -/
public def tensorShortComplexPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) {T : ShortComplex Y.Modules}
    {T' : ShortComplex X.Modules} (σ₁ : (Scheme.Modules.pullback f).obj T.X₁ ≅ T'.X₁)
    (σ₂ : (Scheme.Modules.pullback f).obj T.X₂ ≅ T'.X₂)
    (σ₃ : (Scheme.Modules.pullback f).obj T.X₃ ≅ T'.X₃)
    (h₁₂ : (Scheme.Modules.pullback f).map T.f ≫ σ₂.hom = σ₁.hom ≫ T'.f)
    (h₂₃ : (Scheme.Modules.pullback f).map T.g ≫ σ₃.hom = σ₂.hom ≫ T'.g) (L : Y.Modules)
    (L' : X.Modules) (l : (Scheme.Modules.pullback f).obj L ≅ L')
    [(Stacks.ProjectionFormula.tensorRightInvertible Y L).PreservesZeroMorphisms]
    [(Stacks.ProjectionFormula.tensorRightInvertible X L').PreservesZeroMorphisms] :
    (T.map (Stacks.ProjectionFormula.tensorRightInvertible Y L)).map (Scheme.Modules.pullback f) ≅
      T'.map (Stacks.ProjectionFormula.tensorRightInvertible X L') :=
  ShortComplex.isoMk (tensorPullbackIso f.toLRSHom.toShHom σ₁ l :
      (Scheme.Modules.pullback f).obj
          ((Stacks.ProjectionFormula.tensorRightInvertible Y L).obj T.X₁) ≅
        (Stacks.ProjectionFormula.tensorRightInvertible X L').obj T'.X₁)
    (tensorPullbackIso f.toLRSHom.toShHom σ₂ l :
      (Scheme.Modules.pullback f).obj
          ((Stacks.ProjectionFormula.tensorRightInvertible Y L).obj T.X₂) ≅
        (Stacks.ProjectionFormula.tensorRightInvertible X L').obj T'.X₂)
    (tensorPullbackIso f.toLRSHom.toShHom σ₃ l :
      (Scheme.Modules.pullback f).obj
          ((Stacks.ProjectionFormula.tensorRightInvertible Y L).obj T.X₃) ≅
        (Stacks.ProjectionFormula.tensorRightInvertible X L').obj T'.X₃)
    (tensorPullbackIso_naturality' f σ₁ σ₂ l T.f T'.f h₁₂).symm
    (tensorPullbackIso_naturality' f σ₂ σ₃ l T.g T'.g h₂₃).symm

/-- Composing two commutative ladders. -/
public theorem ladder_comp {C : Type*} [Category C] {X₀ X₁ X₂ Y₀ Y₁ Y₂ Z₀ Z₁ Z₂ : C}
    (c : X₀ ⟶ X₁) (s : X₁ ⟶ X₂) (c' : Z₀ ⟶ Z₁) (s' : Z₁ ⟶ Z₂) (u₀ : X₀ ⟶ Y₀) (v₀ : Y₀ ⟶ Z₀)
    (u₁ : X₁ ⟶ Y₁) (v₁ : Y₁ ⟶ Z₁) (u₂ : X₂ ⟶ Y₂) (v₂ : Y₂ ⟶ Z₂)
    (h₁ : c ≫ u₁ ≫ v₁ = u₀ ≫ v₀ ≫ c') (h₂ : s ≫ u₂ ≫ v₂ = u₁ ≫ v₁ ≫ s') :
    (c ≫ s) ≫ u₂ ≫ v₂ = u₀ ≫ v₀ ≫ c' ≫ s' := by
  rw [Category.assoc, h₂]
  simpa only [Category.assoc] using congrArg (· ≫ s') h₁

/-- Pasting three commutative squares. -/
public theorem paste_three {C : Type*} [Category C] {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (b₁ : B₀ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ B₃)
    (d₀ : A₀ ⟶ B₀) (d₁ : A₁ ⟶ B₁) (d₂ : A₂ ⟶ B₂) (d₃ : A₃ ⟶ B₃)
    (h₁ : d₀ ≫ b₁ = a₁ ≫ d₁) (h₂ : d₁ ≫ b₂ = a₂ ≫ d₂) (h₃ : d₂ ≫ b₃ = a₃ ≫ d₃) :
    d₀ ≫ b₁ ≫ b₂ ≫ b₃ = (a₁ ≫ a₂ ≫ a₃) ≫ d₃ := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc d₁, h₂, Category.assoc, h₃]
  simp only [Category.assoc]

/-- Functor image of a composite, given a commuting square for each factor. -/
private theorem map_comp_comp_of_squares {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B B' : C} {P M Z : D} (a : A ⟶ B) (b : B ⟶ B') (x : F.obj B ⟶ M) (z : F.obj B' ⟶ Z)
    (y : F.obj A ⟶ P) (a' : P ⟶ M) (b' : M ⟶ Z) (h₁ : F.map a ≫ x = y ≫ a')
    (h₂ : F.map b ≫ z = x ≫ b') : F.map (a ≫ b) ≫ z = y ≫ a' ≫ b' := by
  rw [F.map_comp, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

section ProjectionFormula

variable {X X' T : Scheme.{u}} (f : X' ⟶ X) [IsIso f] (p : X ⟶ T) (p' : X' ⟶ T)
  (hbase : f ≫ p = p') {G G' : T.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G'] (g : G ≅ G')

/-- `f^*(p^* G) ≅ p'^* G'`. -/
public abbrev pullbackPullbackIso' :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj G) ≅
      (Scheme.Modules.pullback p').obj G' :=
  pullbackPullbackIso f p p' hbase G ≪≫ (Scheme.Modules.pullback p').mapIso g

/-- `f^*(- ⊗ p^* G) ≅ f^*(-) ⊗ p'^* G'`. -/
public def tensorPullbackNatIso :
    Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback p).obj G) ⋙
        Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙
        Stacks.ProjectionFormula.tensorRightInvertible X' ((Scheme.Modules.pullback p').obj G') :=
  NatIso.ofComponents
    (fun F => (tensorPullbackIso f.toLRSHom.toShHom (Iso.refl _)
        (pullbackPullbackIso' f p p' hbase g) :
      (Scheme.Modules.pullback f).obj
          ((Stacks.ProjectionFormula.tensorRightInvertible X
            ((Scheme.Modules.pullback p).obj G)).obj F) ≅
        (Stacks.ProjectionFormula.tensorRightInvertible X'
            ((Scheme.Modules.pullback p').obj G')).obj
          ((Scheme.Modules.pullback f).obj F)))
    (fun {_ _} φ => tensorPullbackIso_naturality' f (Iso.refl _) (Iso.refl _) _ φ
      ((Scheme.Modules.pullback f).map φ) ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- Tensoring with an isomorphism `G ≅ G'`, as a natural transformation. -/
public def tensorRightNatTrans {Z : Scheme.{u}} {H H' : Z.Modules} (h : H ⟶ H') :
    Stacks.ProjectionFormula.tensorRightInvertible Z H ⟶
      Stacks.ProjectionFormula.tensorRightInvertible Z H' where
  app F := tensorMap (Z := Z.toRingedSpace) (𝟙 F) h
  naturality {F F'} φ :=
    (tensorMap_comp (Z := Z.toRingedSpace) φ (𝟙 F') (𝟙 H) h).trans
      ((congrArg₂ (tensorMap (Z := Z.toRingedSpace)) (Category.comp_id φ)
          (Category.id_comp h)).trans
        ((congrArg₂ (tensorMap (Z := Z.toRingedSpace)) (Category.id_comp φ)
          (Category.comp_id h)).symm.trans
          (tensorMap_comp (Z := Z.toRingedSpace) (𝟙 F) φ h (𝟙 H')).symm))

/-- `p_* ≅ p'_* ∘ f^*` on a section, for `p' = f ≫ p`: the pullback unit. -/
public theorem pushforwardPullbackIso_hom_app_rfl (M : X.Modules) (U : T.Opens)
    (x : M.val.obj (op (p ⁻¹ᵁ U))) :
    ((pushforwardPullbackIso f p (f ≫ p) rfl).hom.app M).val.app (op U) x =
      pbUnit f M (p ⁻¹ᵁ U) x := by
  exact ConcreteCategory.congr_hom
    (pushforwardCongr_rfl_app_app f p ((Scheme.Modules.pullback f).obj M) U) _

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G'] in
/-- **The projection formula in degree zero under pullback along an isomorphism.** -/
public theorem projectionFormulaMap_pullback (F : X.Modules) :
    tensorMap (Z := T.toRingedSpace) ((pushforwardPullbackIso f p p' hbase).hom.app F) g.hom ≫
        (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans p' G').app
          ((Scheme.Modules.pullback f).obj F) =
      (Stacks.ProjectionFormula.pushforwardTensorRightNatTrans p G).app F ≫
        (pushforwardPullbackIso f p p' hbase).hom.app _ ≫
        (Scheme.Modules.pushforward p').map ((tensorPullbackNatIso f p p' hbase g).hom.app F) := by
  subst hbase
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := T.sheaf) fun U s t => ?_
  have hα := pushforwardPullbackIso_hom_app_rfl f p F U.unop s
  have hP := projectionFormulaMap'_unit_tmul (f ≫ p).toLRSHom.toShHom
    ((Scheme.Modules.pullback f).obj F)
    G' U ((pushforwardPullbackIso f p (f ≫ p) rfl).hom.app F |>.val.app U s) (g.hom.val.app U t)
  have hP' := projectionFormulaMap'_unit_tmul p.toLRSHom.toShHom F G U s t
  have hα' := pushforwardPullbackIso_hom_app_rfl f p
    ((Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback p).obj G)).obj F)
    U.unop ((tensorSheafUnit (Osharp := X.sheaf) F ((pullbackFunctor p.toLRSHom.toShHom).obj G)).app
      ((opensMap p.toLRSHom.toShHom).op.obj U) (s ⊗ₜ pullbackUnit p.toLRSHom.toShHom G U t))
  have hΨ := tensorPullbackIso_unit f.toLRSHom.toShHom
    (Iso.refl ((Scheme.Modules.pullback f).obj F))
    (pullbackPullbackIso' f p (f ≫ p) rfl g) ((opensMap p.toLRSHom.toShHom).op.obj U) s
    (pullbackUnit p.toLRSHom.toShHom G U t)
  have hpp := pullbackPullbackIso_rfl_pbUnit f p G U.unop t
  have hg : pbUnit (f ≫ p) G' U.unop (g.hom.val.app U t) =
      ((Scheme.Modules.pullback (f ≫ p)).map g.hom).val.app _ (pbUnit (f ≫ p) G U.unop t) :=
    congrArg (fun φ => φ.val.app U t)
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ p)).unit.naturality g.hom)
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ _ _) ?_
  refine Eq.trans (congrArg
    (((Stacks.ProjectionFormula.pushforwardTensorRightNatTrans (f ≫ p) G').app
      ((Scheme.Modules.pullback f).obj F)).val.app U)
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology T.carrier) (Osharp := T.sheaf)
      (f := (pushforwardPullbackIso f p (f ≫ p) rfl).hom.app F) (g := g.hom) (V := U) _ _ _ _)) ?_
  refine Eq.trans hP ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine Eq.trans ?_ (congrArg ((((pushforwardPullbackIso f p (f ≫ p) rfl).hom.app _ ≫
    (Scheme.Modules.pushforward (f ≫ p)).map
      ((tensorPullbackNatIso f p (f ≫ p) rfl g).hom.app F))).val.app U) hP').symm
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine Eq.trans ?_ (congrArg (((Scheme.Modules.pushforward (f ≫ p)).map
      ((tensorPullbackNatIso f p (f ≫ p) rfl g).hom.app F)).val.app U) hα').symm
  refine Eq.trans ?_ hΨ.symm
  refine congrArg₂ (fun a b => (tensorSheafUnit (Osharp := X'.sheaf) _ _).app _ (a ⊗ₜ b)) hα ?_
  refine Eq.trans hg ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  exact (congrArg (((Scheme.Modules.pullback (f ≫ p)).map g.hom).val.app _) hpp).symm

/-- The comparison of the projection formulas of `p` and of `p'`, as a morphism of δ-functors,
that applies the projection formula of `p`, then the comparison of direct images along `f`, then
tensoring with `g`. -/
public def projectionFormulaPullbackLeft :
    projectionSourceDelta p G ⟶ ((pushDelta p').precomp (Scheme.Modules.pullback f)).postcomp
      (Stacks.ProjectionFormula.tensorRightInvertible T G') :=
  (projectionFormulaDelta p G).hom ≫
    DeltaFunctor.postcompHom (Stacks.ProjectionFormula.tensorRightInvertible T G)
      (directImageComparison p p' (Scheme.Modules.pullback f)
        (pushforwardPullbackIso f p p' hbase)).hom ≫
    DeltaFunctor.postcompNatTrans ((pushDelta p').precomp (Scheme.Modules.pullback f))
      (Stacks.ProjectionFormula.tensorRightInvertible T G) (tensorRightNatTrans g.hom)

/-- The comparison of the projection formulas of `p` and of `p'`, as a morphism of δ-functors,
that applies the comparison of direct images along `f`, then the pullback of the tensor product,
then the projection formula of `p'`. -/
public def projectionFormulaPullbackRight :
    projectionSourceDelta p G ⟶ ((pushDelta p').precomp (Scheme.Modules.pullback f)).postcomp
      (Stacks.ProjectionFormula.tensorRightInvertible T G') where
  app q :=
    { app := fun F => (directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q _).hom ≫
        ((Scheme.Modules.pushforward p').rightDerived q).map
          ((tensorPullbackNatIso f p p' hbase g).hom.app F) ≫
        (projectionFormulaDeltaApp p' G' ((Scheme.Modules.pullback f).obj F) q).hom
      naturality := fun {_ _} φ =>
        paste_three _ _ _ _ _ _ _ _ _ _
          (directImageComparisonApp_naturality p p' (Scheme.Modules.pullback f)
            (pushforwardPullbackIso f p p' hbase) q _)
          (((Scheme.Modules.pushforward p').rightDerived q).map_comp _ _ |>.symm.trans
            ((congrArg ((Scheme.Modules.pushforward p').rightDerived q).map
              ((tensorPullbackNatIso f p p' hbase g).hom.naturality φ)).trans
              (((Scheme.Modules.pushforward p').rightDerived q).map_comp _ _)))
          (((projectionFormulaDelta p' G').hom.app q).naturality
            ((Scheme.Modules.pullback f).map φ)) }
  comm {S} hS q :=
    (paste_three _ _ _ _ _ _ _ _ _ _
      (directImageComparisonApp_δ p p' (Scheme.Modules.pullback f)
        (pushforwardPullbackIso f p p' hbase) (hS.map_of_exact
          (Stacks.ProjectionFormula.tensorRightInvertible X
            ((Scheme.Modules.pullback p).obj G))) q).symm
      ((pushDelta p').δ_naturality
        ((hS.map_of_exact (Stacks.ProjectionFormula.tensorRightInvertible X
          ((Scheme.Modules.pullback p).obj G))).map_of_exact (Scheme.Modules.pullback f))
        ((hS.map_of_exact (Scheme.Modules.pullback f)).map_of_exact
          (Stacks.ProjectionFormula.tensorRightInvertible X' ((Scheme.Modules.pullback p').obj G')))
        ({ τ₁ := (tensorPullbackNatIso f p p' hbase g).hom.app S.X₁,
           τ₂ := (tensorPullbackNatIso f p p' hbase g).hom.app S.X₂,
           τ₃ := (tensorPullbackNatIso f p p' hbase g).hom.app S.X₃,
           comm₁₂ := ((tensorPullbackNatIso f p p' hbase g).hom.naturality S.f).symm,
           comm₂₃ := ((tensorPullbackNatIso f p p' hbase g).hom.naturality S.g).symm } :
          (S.map (Stacks.ProjectionFormula.tensorRightInvertible X
              ((Scheme.Modules.pullback p).obj G))).map
              (Scheme.Modules.pullback f) ⟶
            (S.map (Scheme.Modules.pullback f)).map
              (Stacks.ProjectionFormula.tensorRightInvertible X'
              ((Scheme.Modules.pullback p').obj G'))) q).symm
      ((projectionFormulaDelta p' G').hom.comm
        (hS.map_of_exact (Scheme.Modules.pullback f)) q).symm).symm

/-- Two composites agree given three commuting relations and a retraction `i ≫ k = 𝟙`. -/
private theorem zero_chase {C : Type*} [Category C] {A₀ A₁ B B₂ B₃ Z P₀ P₁ Q₀ Q₁ Y' : C}
    {r : A₀ ⟶ A₁} {n : A₁ ⟶ B} {u : B ⟶ B₂} {v : B₂ ⟶ B₃} {w : B₃ ⟶ Z} {c : B ⟶ Y'}
    {t : Y' ⟶ Z} {a : A₁ ⟶ P₁} {ps : P₁ ⟶ Q₁} {n' : Q₁ ⟶ Y'} {i : P₁ ⟶ P₀} {s : P₀ ⟶ Q₀}
    {j : Q₀ ⟶ Q₁} {k : P₀ ⟶ P₁}
    (huvw : u ≫ v ≫ w = c ≫ t) (hnc : n ≫ c = a ≫ ps ≫ n') (hsj : s ≫ j = k ≫ ps)
    (hik : i ≫ k = 𝟙 _) :
    (r ≫ n ≫ u) ≫ v ≫ w = (r ≫ a ≫ i) ≫ s ≫ j ≫ n' ≫ t := by
  simp only [Category.assoc, huvw, reassoc_of% hnc, reassoc_of% hsj, reassoc_of% hik]

/-- The two comparisons agree in degree zero. -/
public theorem projectionFormulaPullback_zero (F : X.Modules) :
    ((projectionFormulaPullbackLeft f p p' hbase g).app 0).app F =
      ((projectionFormulaPullbackRight f p p' hbase g).app 0).app F := by
  have hL :
      ((projectionFormulaDelta p G).hom.app 0).app F = (projectionFormulaZero p G).hom.app F :=
    congrArg (fun η => NatTrans.app η F)
      (DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (projectionFormulaZero p G))
  have hR : ((projectionFormulaDelta p' G').hom.app 0).app ((Scheme.Modules.pullback f).obj F) =
      (projectionFormulaZero p' G').hom.app ((Scheme.Modules.pullback f).obj F) :=
    congrArg (fun η => NatTrans.app η ((Scheme.Modules.pullback f).obj F))
      (DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (projectionFormulaZero p' G'))
  have hτ := directImageComparisonApp_zero p p' (Scheme.Modules.pullback f)
    (pushforwardPullbackIso f p p' hbase) F
  have hτ' := directImageComparisonApp_zero p p' (Scheme.Modules.pullback f)
    (pushforwardPullbackIso f p p' hbase)
    ((Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback p).obj G)).obj F)
  have h0 := projectionFormulaMap_pullback f p p' hbase g F
  show CategoryStruct.comp
    (X := (((Scheme.Modules.pushforward p).rightDerived 0).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible X
        ((Scheme.Modules.pullback p).obj G)).obj F)))
    (Y := ((Stacks.ProjectionFormula.tensorRightInvertible T G).obj
      (((Scheme.Modules.pushforward p).rightDerived 0).obj F)))
    (Z := ((Stacks.ProjectionFormula.tensorRightInvertible T G').obj
      (((Scheme.Modules.pushforward p').rightDerived 0).obj ((Scheme.Modules.pullback f).obj F))))
      ((projectionFormulaDelta p G).hom.app 0 |>.app F)
      (CategoryStruct.comp
        (X := ((Stacks.ProjectionFormula.tensorRightInvertible T G).obj
          (((Scheme.Modules.pushforward p).rightDerived 0).obj F)))
        (Y := ((Stacks.ProjectionFormula.tensorRightInvertible T G).obj
          (((Scheme.Modules.pushforward p').rightDerived 0).obj
            ((Scheme.Modules.pullback f).obj F))))
        (Z := ((Stacks.ProjectionFormula.tensorRightInvertible T G').obj
          (((Scheme.Modules.pushforward p').rightDerived 0).obj
            ((Scheme.Modules.pullback f).obj F))))
        ((Stacks.ProjectionFormula.tensorRightInvertible T G).map
          (directImageComparisonApp p p' (Scheme.Modules.pullback f)
            (pushforwardPullbackIso f p p' hbase) 0 F).hom)
        ((tensorRightNatTrans g.hom).app (((Scheme.Modules.pushforward p').rightDerived 0).obj
          ((Scheme.Modules.pullback f).obj F)))) =
    CategoryStruct.comp
      (X := (((Scheme.Modules.pushforward p).rightDerived 0).obj
        ((Stacks.ProjectionFormula.tensorRightInvertible X
          ((Scheme.Modules.pullback p).obj G)).obj F)))
      (Y := (((Scheme.Modules.pushforward p').rightDerived 0).obj
        ((Scheme.Modules.pullback f).obj
          ((Stacks.ProjectionFormula.tensorRightInvertible X
            ((Scheme.Modules.pullback p).obj G)).obj F))))
      (Z := ((Stacks.ProjectionFormula.tensorRightInvertible T G').obj
        (((Scheme.Modules.pushforward p').rightDerived 0).obj ((Scheme.Modules.pullback f).obj F))))
      (directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) 0
          ((Stacks.ProjectionFormula.tensorRightInvertible X
            ((Scheme.Modules.pullback p).obj G)).obj F)).hom
      (CategoryStruct.comp
        (X := (((Scheme.Modules.pushforward p').rightDerived 0).obj
          ((Scheme.Modules.pullback f).obj
            ((Stacks.ProjectionFormula.tensorRightInvertible X
              ((Scheme.Modules.pullback p).obj G)).obj F))))
        (Y := (((Scheme.Modules.pushforward p').rightDerived 0).obj
          ((Stacks.ProjectionFormula.tensorRightInvertible X'
            ((Scheme.Modules.pullback p').obj G')).obj ((Scheme.Modules.pullback f).obj F))))
        (Z := ((Stacks.ProjectionFormula.tensorRightInvertible T G').obj
          (((Scheme.Modules.pushforward p').rightDerived 0).obj
            ((Scheme.Modules.pullback f).obj F))))
        (((Scheme.Modules.pushforward p').rightDerived 0).map
          ((tensorPullbackNatIso f p p' hbase g).hom.app F))
        ((projectionFormulaDelta p' G').hom.app 0 |>.app ((Scheme.Modules.pullback f).obj F)))
  rw [hL, hR, hτ, hτ']
  have h0' :
      (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p G).hom.app F ≫
      (tensorMap (Z := T.toRingedSpace) ((pushforwardPullbackIso f p p' hbase).hom.app F) g.hom :
        (Stacks.ProjectionFormula.tensorRightInvertible T G).obj
            ((Scheme.Modules.pushforward p).obj F) ⟶
          (Stacks.ProjectionFormula.tensorRightInvertible T G').obj
            ((Scheme.Modules.pushforward p').obj ((Scheme.Modules.pullback f).obj F))) =
      (pushforwardPullbackIso f p p' hbase).hom.app _ ≫
        (Scheme.Modules.pushforward p').map ((tensorPullbackNatIso f p p' hbase g).hom.app F) ≫
        (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p' G').hom.app
          ((Scheme.Modules.pullback f).obj F) := by
    have h0'' :
        tensorMap (Z := T.toRingedSpace) ((pushforwardPullbackIso f p p' hbase).hom.app F) g.hom ≫
        (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p' G').inv.app
          ((Scheme.Modules.pullback f).obj F) =
        (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p G).inv.app F ≫
        (pushforwardPullbackIso f p p' hbase).hom.app _ ≫
        (Scheme.Modules.pushforward p').map ((tensorPullbackNatIso f p p' hbase g).hom.app F) := h0
    exact (iso_square_inv
      (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p G |>.app F).symm
      (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p' G' |>.app
        ((Scheme.Modules.pullback f).obj F)).symm _ _ h0''.symm).trans (Category.assoc _ _ _)
  have hZ : (projectionFormulaZero p G).hom.app F =
      (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p)).hom.app
          ((Stacks.ProjectionFormula.tensorRightInvertible X
            ((Scheme.Modules.pullback p).obj G)).obj F) ≫
        (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p G).hom.app F ≫
        (Stacks.ProjectionFormula.tensorRightInvertible T G).map
          ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p)).inv.app F) := rfl
  have hZ' : (projectionFormulaZero p' G').hom.app ((Scheme.Modules.pullback f).obj F) =
      (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).hom.app
          ((Stacks.ProjectionFormula.tensorRightInvertible X'
            ((Scheme.Modules.pullback p').obj G')).obj
            ((Scheme.Modules.pullback f).obj F)) ≫
        (Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p' G').hom.app
          ((Scheme.Modules.pullback f).obj F) ≫
        (Stacks.ProjectionFormula.tensorRightInvertible T G').map
          ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).inv.app
            ((Scheme.Modules.pullback f).obj F)) := rfl
  rw [hZ, hZ']
  have hsj : ((Scheme.Modules.pushforward p').rightDerived 0).map
        ((tensorPullbackNatIso f p p' hbase g).hom.app F) ≫
      (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).hom.app
          ((Stacks.ProjectionFormula.tensorRightInvertible X'
            ((Scheme.Modules.pullback p').obj G')).obj
            ((Scheme.Modules.pullback f).obj F)) =
      (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).hom.app _ ≫
        (Scheme.Modules.pushforward p').map ((tensorPullbackNatIso f p p' hbase g).hom.app F) :=
    (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).hom.naturality _
  have hik := Iso.inv_hom_id_app (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p'))
    ((Scheme.Modules.pullback f).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible X
        ((Scheme.Modules.pullback p).obj G)).obj F))
  have hc : (tensorRightNatTrans g.hom).app
        ((Scheme.Modules.pushforward p).obj F) ≫
      (Stacks.ProjectionFormula.tensorRightInvertible T G').map
        ((pushforwardPullbackIso f p p' hbase).hom.app F) =
      tensorMap (Z := T.toRingedSpace) ((pushforwardPullbackIso f p p' hbase).hom.app F) g.hom :=
    (tensorMap_comp (Z := T.toRingedSpace) (𝟙 _)
      ((pushforwardPullbackIso f p p' hbase).hom.app F) g.hom (𝟙 G')).trans
      (congrArg₂ (fun a b => tensorMap (Z := T.toRingedSpace) a b)
        (Category.id_comp _) (Category.comp_id _))
  have h0n := (congrArg
    ((Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso p G).hom.app F ≫ ·)
    hc).trans h0'
  have huvw : (Stacks.ProjectionFormula.tensorRightInvertible T G).map
        ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p)).inv.app F) ≫
      (Stacks.ProjectionFormula.tensorRightInvertible T G).map
        ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p)).hom.app F ≫
          (pushforwardPullbackIso f p p' hbase).hom.app F ≫
          (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).inv.app
            ((Scheme.Modules.pullback f).obj F)) ≫
      (tensorRightNatTrans g.hom).app (((Scheme.Modules.pushforward p').rightDerived 0).obj
          ((Scheme.Modules.pullback f).obj F)) =
      ((tensorRightNatTrans g.hom).app ((Scheme.Modules.pushforward p).obj F) ≫
        (Stacks.ProjectionFormula.tensorRightInvertible T G').map
          ((pushforwardPullbackIso f p p' hbase).hom.app F)) ≫
      (Stacks.ProjectionFormula.tensorRightInvertible T G').map
          ((rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).inv.app
            ((Scheme.Modules.pullback f).obj F)) :=
    ((Functor.map_comp_assoc _ _ _ _).symm.trans (congrArg
      (fun x => (Stacks.ProjectionFormula.tensorRightInvertible T G).map x ≫
        (tensorRightNatTrans g.hom).app _)
      (Iso.inv_hom_id_app_assoc _ _ _))).trans (((tensorRightNatTrans g.hom).naturality _).trans
        ((congrArg ((tensorRightNatTrans g.hom).app _ ≫ ·)
          ((Stacks.ProjectionFormula.tensorRightInvertible T G').map_comp _ _)).trans
          (Category.assoc _ _ _).symm))
  exact zero_chase (r := (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p)).hom.app
    ((Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback p).obj G)).obj F))
    huvw h0n hsj hik

/-- **The projection formulas of the two bundles correspond**, in every degree. -/
public theorem projectionFormulaDeltaApp_pullback (q : ℕ) (F : X.Modules) :
    (projectionFormulaDeltaApp p G F q).hom ≫
        tensorMap (Z := T.toRingedSpace) (directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q F).hom g.hom =
      (directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q _).hom ≫
        ((Scheme.Modules.pushforward p').rightDerived q).map
          ((tensorPullbackNatIso f p p' hbase g).hom.app F) ≫
        (projectionFormulaDeltaApp p' G' ((Scheme.Modules.pullback f).obj F) q).hom := by
  have h := DeltaFunctor.IsUniversal.hom_ext_zero (projectionSourceDelta p G)
    (η := projectionFormulaPullbackLeft f p p' hbase g)
    (γ := projectionFormulaPullbackRight f p p' hbase g)
    (NatTrans.ext (funext (projectionFormulaPullback_zero f p p' hbase g)))
  refine Eq.trans ?_ (congrArg (fun η => (DeltaFunctor.Hom.app η q).app F) h)
  exact congrArg ((projectionFormulaDeltaApp p G F q).hom ≫ ·)
    ((congrArg₂ (tensorMap (Z := T.toRingedSpace)) (Category.comp_id _).symm
      (Category.id_comp g.hom).symm).trans (tensorMap_comp (Z := T.toRingedSpace) _ _ _ _).symm)

end ProjectionFormula

section KoszulGeneral

open Stacks.SheafOfModules.TopWedge Stacks.SheafOfModules.WedgeQuotient

variable {S S' : Scheme.{u}} {E : S.Modules} {E' : S'.Modules} [E.IsQuasicoherent]
  [E'.IsQuasicoherent]
  {hqc : Stacks.SymGraded.IsQuasicoherentPieces E}
  {hqc' : Stacks.SymGraded.IsQuasicoherentPieces E'}
  {D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)}
  {D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')}
  (f : bundle E' hqc' ⟶ bundle E hqc)
  (θ : ∀ d : ℤ, (Scheme.Modules.pullback f).obj (D.algebra.piece d) ≅ D'.algebra.piece d)
  (lV : (Scheme.Modules.pullback f).obj (bundlePullback E hqc) ≅ bundlePullback E' hqc')
  (hu : (Scheme.Modules.pullback f).map (tautologicalMap E hqc D) ≫ (θ ((1 : ℕ) : ℤ)).hom =
    lV.hom ≫ tautologicalMap E' hqc' D')
  (hmul : ∀ i j : ℤ, (Scheme.Modules.pullback f).map (twistMul D i j) ≫ (θ (i + j)).hom =
    (tensorPullbackIso f.toLRSHom.toShHom (θ i) (θ j)).hom ≫ twistMul D' i j)

variable (κ : (Scheme.Modules.pullback f).obj (tautologicalKernel E hqc D) ≅
    tautologicalKernel E' hqc' D')
  (hκ : (Scheme.Modules.pullback f).map (kernel.ι (tautologicalMap E hqc D)) ≫ lV.hom =
    κ.hom ≫ kernel.ι (tautologicalMap E' hqc' D'))

/-- `f^*(⋀ᵖ K) ≅ ⋀ᵖ K'`. -/
public abbrev kerExtIsoOf (p : ℤ) :
    (Scheme.Modules.pullback f).obj ((kernelAlgebras E hqc D).exterior.piece p) ≅
      (kernelAlgebras E' hqc' D').exterior.piece p :=
  extPullbackIso f.toLRSHom.toShHom (kernelAlgebras E hqc D) (kernelAlgebras E' hqc' D')
    κ p

/-- `f^*(⋀ᵖ π^* E) ≅ ⋀ᵖ π'^* E'`. -/
public abbrev pbExtIso (p : ℤ) :
    (Scheme.Modules.pullback f).obj ((pullbackAlgebras E hqc).exterior.piece p) ≅
      (pullbackAlgebras E' hqc').exterior.piece p :=
  extPullbackIso f.toLRSHom.toShHom (pullbackAlgebras E hqc) (pullbackAlgebras E' hqc') lV p

include hu in
/-- The comparison `⋀ᵖ K ⊗ 𝒪(1) ≅ ⋀ᵖ⁺¹ π^* E / ⋀ᵖ⁺¹ K` corresponds under pullback. -/
public theorem koszulQuotientIso_pullback_of (p : ℕ) :
    (Scheme.Modules.pullback f).map (koszulQuotientIso E hqc D p).inv ≫
        (tensorPullbackIso f.toLRSHom.toShHom (kerExtIsoOf f κ p) (θ ((1 : ℕ) : ℤ))).hom =
      (cokernelPullbackIso f.toLRSHom.toShHom (kernelAlgebras E hqc D) (pullbackAlgebras E hqc)
          (kernelAlgebras E' hqc' D') (pullbackAlgebras E' hqc') _ _ κ lV
          hκ (p + 1)).hom ≫ (koszulQuotientIso E' hqc' D' p).inv := by
  have := epi_tautologicalMap E hqc D
  have := epi_tautologicalMap E' hqc' D'
  have h := cokernelPullbackIso_wedgeQuotient f.toLRSHom.toShHom (kernelAlgebras E hqc D)
    (pullbackAlgebras E hqc) (kernelAlgebras E' hqc' D') (pullbackAlgebras E' hqc')
    (tautologicalSequence E hqc D).f (tautologicalSequence E' hqc' D').f
    κ lV hκ (tautologicalSequence E hqc D).g
    (tautologicalSequence E' hqc' D').g (tautologicalSequence E hqc D).zero
    (tautologicalSequence E' hqc' D').zero
    (exact_tautological E hqc D) (exact_tautological E' hqc' D') (θ ((1 : ℕ) : ℤ)) hu p
    (ht := epi_tautologicalMap E hqc D) (ht' := epi_tautologicalMap E' hqc' D')
  exact iso_square_inv ((Scheme.Modules.pullback f).mapIso (koszulQuotientIso E hqc D p))
    (koszulQuotientIso E' hqc' D' p) _ _ h

include hκ in
/-- The first arrow of the Koszul filtration under pullback. -/
public theorem koszulSequence_f_pullback_of (p : ℕ) :
    (Scheme.Modules.pullback f).map (koszulSequence E hqc D p).f ≫
        (pbExtIso f lV ((p + 1 : ℕ) : ℤ)).hom =
      (kerExtIsoOf f κ ((p + 1 : ℕ) : ℤ)).hom ≫ (koszulSequence E' hqc' D' p).f :=
  extPullbackIso_extHom f.toLRSHom.toShHom (kernelAlgebras E hqc D) (pullbackAlgebras E hqc)
    (kernelAlgebras E' hqc' D') (pullbackAlgebras E' hqc') _ _ κ lV
    hκ _

include hu hκ in
/-- The second arrow of the Koszul filtration under pullback. -/
public theorem koszulSequence_g_pullback_of (p : ℕ) :
    (Scheme.Modules.pullback f).map (koszulSequence E hqc D p).g ≫
        (tensorPullbackIso f.toLRSHom.toShHom (kerExtIsoOf f κ p) (θ ((1 : ℕ) : ℤ))).hom =
      (pbExtIso f lV ((p + 1 : ℕ) : ℤ)).hom ≫ (koszulSequence E' hqc' D' p).g := by
  exact map_comp_comp_of_squares _ _ _ _ _ _ _ _
    (cokernelPullbackIso_π f.toLRSHom.toShHom (kernelAlgebras E hqc D) (pullbackAlgebras E hqc)
      (kernelAlgebras E' hqc' D') (pullbackAlgebras E' hqc') _ _ κ lV hκ (p + 1))
    (koszulQuotientIso_pullback_of f θ lV hu κ hκ p)

/-- **The pullback of the twisted Koszul filtration of `𝐏(E)` is that of `𝐏(E')`.** -/
public def koszulTwistSequencePullbackIsoOf (p : ℕ) :
    (koszulTwistSequence E hqc D p).map (Scheme.Modules.pullback f) ≅
      koszulTwistSequence E' hqc' D' p :=
  tensorShortComplexPullbackIso f (T := koszulSequence E hqc D p)
    (T' := koszulSequence E' hqc' D' p)
    (kerExtIsoOf f κ ((p + 1 : ℕ) : ℤ))
    (pbExtIso f lV ((p + 1 : ℕ) : ℤ))
    (tensorPullbackIso f.toLRSHom.toShHom (kerExtIsoOf f κ p) (θ ((1 : ℕ) : ℤ)))
    (koszulSequence_f_pullback_of f lV κ hκ p) (koszulSequence_g_pullback_of f θ lV hu κ hκ p)
    (negTwist E hqc D (p + 1)) (negTwist E' hqc' D' (p + 1)) (θ _)

omit [E.IsQuasicoherent] [E'.IsQuasicoherent] in
/-- The identification of the twists is compatible with the reindexing of degrees. -/
public theorem twist_eqToHom_pullback {i j : ℤ} (h : i = j) :
    (Scheme.Modules.pullback f).map (eqToHom (congrArg D.algebra.piece h)) ≫ (θ j).hom =
      (θ i).hom ≫ eqToHom (congrArg D'.algebra.piece h) := by
  subst h
  exact ((congrArg (· ≫ (θ i).hom) ((Scheme.Modules.pullback f).map_id _)).trans
    (Category.id_comp _)).trans (Category.comp_id _).symm

include hmul in
/-- **`(⋀ᵖ K ⊗ 𝒪(1)) ⊗ 𝒪(-p-1) ≅ ⋀ᵖ K ⊗ 𝒪(-p)` under pullback.** -/
public theorem koszulTwistIso_pullback_of (p : ℕ) :
    (Scheme.Modules.pullback f).map (koszulTwistIso E hqc D p).hom ≫
        (tensorPullbackIso f.toLRSHom.toShHom (kerExtIsoOf f κ p) (θ (-(p : ℤ)))).hom =
      (tensorPullbackIso f.toLRSHom.toShHom
          (tensorPullbackIso f.toLRSHom.toShHom (kerExtIsoOf f κ p) (θ ((1 : ℕ) : ℤ)))
          (θ (-((p + 1 : ℕ) : ℤ)))).hom ≫ (koszulTwistIso E' hqc' D' p).hom := by
  have hk : (Scheme.Modules.pullback f).map (twistMul D ((1 : ℕ) : ℤ) (-((p + 1 : ℕ) : ℤ)) ≫
        eqToHom (congrArg D.algebra.piece (by push_cast; ring))) ≫ (θ (-(p : ℤ))).hom =
      (tensorPullbackIso f.toLRSHom.toShHom (θ ((1 : ℕ) : ℤ)) (θ (-((p + 1 : ℕ) : ℤ)))).hom ≫
        twistMul D' ((1 : ℕ) : ℤ) (-((p + 1 : ℕ) : ℤ)) ≫
          eqToHom (congrArg D'.algebra.piece (by push_cast; ring)) := by
    exact map_comp_comp_of_squares _ _ _ _ _ _ _ _ (hmul _ _)
      (twist_eqToHom_pullback f θ (by push_cast; ring :
        ((1 : ℕ) : ℤ) + -((p + 1 : ℕ) : ℤ) = -(p : ℤ)))
  have h2 := tensorPullbackIso_naturality₂ f.toLRSHom.toShHom (kerExtIsoOf f κ p)
    (kerExtIsoOf f κ p) (tensorPullbackIso f.toLRSHom.toShHom (θ ((1 : ℕ) : ℤ))
      (θ (-((p + 1 : ℕ) : ℤ)))) (θ (-(p : ℤ))) (𝟙 _) (𝟙 _) _ _ (by simp) hk
  have h1 := tensorPullbackIso_assoc f.toLRSHom.toShHom (kerExtIsoOf f κ p) (θ ((1 : ℕ) : ℤ))
    (θ (-((p + 1 : ℕ) : ℤ)))
  refine map_comp_comp_of_squares _ (koszulAssoc E hqc D p).hom (koszulTwistMulIso E hqc D p).hom
    _ _ _ _ _ h1 ?_
  rw [koszulTwistMulIso_hom E hqc D p, koszulTwistMulIso_hom E' hqc' D' p]
  exact h2

/-- `f^*(⋀ᵖ K ⊗ 𝒪(-p)) ≅ ⋀ᵖ K' ⊗ 𝒪'(-p)`. -/
public abbrev koszulTermIsoOf (p : ℕ) :
    (Scheme.Modules.pullback f).obj (koszulTerm E hqc D p) ≅ koszulTerm E' hqc' D' p :=
  tensorPullbackIso f.toLRSHom.toShHom (kerExtIsoOf f κ p) (θ (-(p : ℤ)))

end KoszulGeneral

section Koszul

/-- `HasWeakSheafify J AddCommGrpCat.{u}` at the site's own universe, so that instance search does
not leave a universe of a `max`-universe sheafification instance unsolved. -/
abbrev hasWeakSheafifyAddCommGrpCat_koszulTransport {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) : HasWeakSheafify J AddCommGrpCat.{u} :=
  inferInstance

attribute [local instance high] hasWeakSheafifyAddCommGrpCat_koszulTransport

open Stacks.SheafOfModules.TopWedge Stacks.SheafOfModules.WedgeQuotient

variable {S : Scheme.{u}} {E E' : S.Modules} [E.IsQuasicoherent] [E'.IsQuasicoherent]
  {hqc : Stacks.SymGraded.IsQuasicoherentPieces E}
  {hqc' : Stacks.SymGraded.IsQuasicoherentPieces E'}
  {D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)}
  {D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')}
  (f : bundle E' hqc' ⟶ bundle E hqc) [IsIso f]
  (θ : ∀ d : ℤ, (Scheme.Modules.pullback f).obj (D.algebra.piece d) ≅ D'.algebra.piece d)
  (lV : (Scheme.Modules.pullback f).obj (bundlePullback E hqc) ≅ bundlePullback E' hqc')
  (hu : (Scheme.Modules.pullback f).map (tautologicalMap E hqc D) ≫ (θ ((1 : ℕ) : ℤ)).hom =
    lV.hom ≫ tautologicalMap E' hqc' D')
  (hmul : ∀ i j : ℤ, (Scheme.Modules.pullback f).map (twistMul D i j) ≫ (θ (i + j)).hom =
    (tensorPullbackIso f.toLRSHom.toShHom (θ i) (θ j)).hom ≫ twistMul D' i j)

/-- **`f^* K ≅ K'`**: the kernels of the tautological surjections correspond. -/
public def tautKernelIso :
    (Scheme.Modules.pullback f).obj (tautologicalKernel E hqc D) ≅ tautologicalKernel E' hqc' D' :=
  kernelIsoOfIso (Scheme.Modules.pullback f) (tautologicalMap E hqc D) (tautologicalMap E' hqc' D')
    lV (θ ((1 : ℕ) : ℤ)) hu

omit [E.IsQuasicoherent] [E'.IsQuasicoherent] in
/-- The kernel inclusions correspond. -/
public theorem tautKernelIso_ι :
    (Scheme.Modules.pullback f).map (kernel.ι (tautologicalMap E hqc D)) ≫ lV.hom =
      (tautKernelIso f θ lV hu).hom ≫ kernel.ι (tautologicalMap E' hqc' D') :=
  kernelIsoOfIso_ι _ _ _ _ _ hu

/-- `f^*(⋀ᵖ K) ≅ ⋀ᵖ K'`. -/
public abbrev kerExtIso (p : ℤ) :
    (Scheme.Modules.pullback f).obj ((kernelAlgebras E hqc D).exterior.piece p) ≅
      (kernelAlgebras E' hqc' D').exterior.piece p :=
  kerExtIsoOf f (tautKernelIso f θ lV hu) p

/-- The comparison `⋀ᵖ K ⊗ 𝒪(1) ≅ ⋀ᵖ⁺¹ π^* E / ⋀ᵖ⁺¹ K` corresponds under pullback. -/
public theorem koszulQuotientIso_pullback (p : ℕ) :
    (Scheme.Modules.pullback f).map (koszulQuotientIso E hqc D p).inv ≫
        (tensorPullbackIso f.toLRSHom.toShHom (kerExtIso f θ lV hu p) (θ ((1 : ℕ) : ℤ))).hom =
      (cokernelPullbackIso f.toLRSHom.toShHom (kernelAlgebras E hqc D) (pullbackAlgebras E hqc)
          (kernelAlgebras E' hqc' D') (pullbackAlgebras E' hqc') _ _ (tautKernelIso f θ lV hu) lV
          (tautKernelIso_ι f θ lV hu) (p + 1)).hom ≫ (koszulQuotientIso E' hqc' D' p).inv :=
  koszulQuotientIso_pullback_of f θ lV hu _ (tautKernelIso_ι f θ lV hu) p

/-- The first arrow of the Koszul filtration under pullback. -/
public theorem koszulSequence_f_pullback (p : ℕ) :
    (Scheme.Modules.pullback f).map (koszulSequence E hqc D p).f ≫
        (pbExtIso f lV ((p + 1 : ℕ) : ℤ)).hom =
      (kerExtIso f θ lV hu ((p + 1 : ℕ) : ℤ)).hom ≫ (koszulSequence E' hqc' D' p).f :=
  koszulSequence_f_pullback_of f lV _ (tautKernelIso_ι f θ lV hu) p

/-- The second arrow of the Koszul filtration under pullback. -/
public theorem koszulSequence_g_pullback (p : ℕ) :
    (Scheme.Modules.pullback f).map (koszulSequence E hqc D p).g ≫
        (tensorPullbackIso f.toLRSHom.toShHom (kerExtIso f θ lV hu p) (θ ((1 : ℕ) : ℤ))).hom =
      (pbExtIso f lV ((p + 1 : ℕ) : ℤ)).hom ≫ (koszulSequence E' hqc' D' p).g :=
  koszulSequence_g_pullback_of f θ lV hu _ (tautKernelIso_ι f θ lV hu) p

/-- **The pullback of the twisted Koszul filtration of `𝐏(E)` is that of `𝐏(E')`.** -/
public abbrev koszulTwistSequencePullbackIso (p : ℕ) :
    (koszulTwistSequence E hqc D p).map (Scheme.Modules.pullback f) ≅
      koszulTwistSequence E' hqc' D' p :=
  koszulTwistSequencePullbackIsoOf f θ lV hu _ (tautKernelIso_ι f θ lV hu) p

include hmul in
/-- **`(⋀ᵖ K ⊗ 𝒪(1)) ⊗ 𝒪(-p-1) ≅ ⋀ᵖ K ⊗ 𝒪(-p)` under pullback.** -/
public theorem koszulTwistIso_pullback (p : ℕ) :
    (Scheme.Modules.pullback f).map (koszulTwistIso E hqc D p).hom ≫
        (tensorPullbackIso f.toLRSHom.toShHom (kerExtIso f θ lV hu p) (θ (-(p : ℤ)))).hom =
      (tensorPullbackIso f.toLRSHom.toShHom
          (tensorPullbackIso f.toLRSHom.toShHom (kerExtIso f θ lV hu p) (θ ((1 : ℕ) : ℤ)))
          (θ (-((p + 1 : ℕ) : ℤ)))).hom ≫ (koszulTwistIso E' hqc' D' p).hom :=
  koszulTwistIso_pullback_of f θ hmul (tautKernelIso f θ lV hu) p

/-- `f^*(⋀ᵖ K ⊗ 𝒪(-p)) ≅ ⋀ᵖ K' ⊗ 𝒪'(-p)`. -/
public abbrev koszulTermIso (p : ℕ) :
    (Scheme.Modules.pullback f).obj (koszulTerm E hqc D p) ≅ koszulTerm E' hqc' D' p :=
  koszulTermIsoOf f θ (tautKernelIso f θ lV hu) p

variable (hbase : f ≫ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase =
  (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase)

/-- The comparison `R^q π_* ≅ R^q π'_* ∘ f^*` at a module. -/
public abbrev bundleComparison (q : ℕ) (M : (bundle E hqc).Modules) :=
  directImageComparisonApp _ _ (Scheme.Modules.pullback f) (pushforwardPullbackIso f _ _ hbase) q M

variable {n : ℕ} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1))

include hmul in
/-- **The dimension-shifting isomorphisms of the Koszul filtration correspond under `f`.** -/
public theorem koszulShiftIso_pullback {p : ℕ} (hp : p + 1 ≤ n) (q : ℕ) :
    (koszulShiftIso E hqc D hn hfree hp q).hom ≫ (bundleComparison f hbase (q + 1) _).hom ≫
        ((bundlePushforward E' hqc').rightDerived (q + 1)).map
          (koszulTermIso f θ lV hu (p + 1)).hom =
      (bundleComparison f hbase q _).hom ≫
        ((bundlePushforward E' hqc').rightDerived q).map (koszulTermIso f θ lV hu p).hom ≫
        (koszulShiftIso E' hqc' D' hn hfree' hp q).hom := by
  have hδ := directImageComparisonApp_δ _ _ (Scheme.Modules.pullback f)
    (pushforwardPullbackIso f _ _ hbase) (shortExact_koszulTwistSequence E hqc D p) q
  have hnat := (pushDelta (relativeProj
    (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).δ_naturality
    ((shortExact_koszulTwistSequence E hqc D p).map_of_exact (Scheme.Modules.pullback f))
    (shortExact_koszulTwistSequence E' hqc' D' p) (koszulTwistSequencePullbackIso f θ lV hu p).hom q
  have hτ := directImageComparisonApp_naturality _ _ (Scheme.Modules.pullback f)
    (pushforwardPullbackIso f _ _ hbase) q (koszulTwistIso E hqc D p).inv
  have hsq := iso_square_inv ((Scheme.Modules.pullback f).mapIso (koszulTwistIso E hqc D p))
    (koszulTwistIso E' hqc' D' p) _ _ (koszulTwistIso_pullback f θ lV hu hmul p)
  show (((bundlePushforward E hqc).rightDerived q).map (koszulTwistIso E hqc D p).inv ≫
      (pushDelta _).δ (shortExact_koszulTwistSequence E hqc D p) q) ≫ _ ≫ _ =
    _ ≫ _ ≫ ((bundlePushforward E' hqc').rightDerived q).map (koszulTwistIso E' hqc' D' p).inv ≫
      (pushDelta _).δ (shortExact_koszulTwistSequence E' hqc' D' p) q
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (((bundlePushforward E hqc).rightDerived q).map
      (koszulTwistIso E hqc D p).inv ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ((bundlePushforward E' hqc').rightDerived (q + 1)).map
        (koszulTermIso f θ lV hu (p + 1)).hom) hδ.symm).trans (Category.assoc _ _ _)))).trans ?_
  refine (congrArg (fun φ => ((bundlePushforward E hqc).rightDerived q).map
      (koszulTwistIso E hqc D p).inv ≫ (bundleComparison f hbase q _).hom ≫ φ) hnat.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hτ).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg ((bundleComparison f hbase q _).hom ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _)
    (((bundlePushforward E' hqc').rightDerived q).map_comp _ _).symm).trans ?_
  refine (congrArg (fun φ => ((bundlePushforward E' hqc').rightDerived q).map φ ≫
    (pushDelta _).δ (shortExact_koszulTwistSequence E' hqc' D' p) q) hsq).trans ?_
  refine (congrArg (· ≫ _) (((bundlePushforward E' hqc').rightDerived q).map_comp _ _)).trans ?_
  exact Category.assoc _ _ _

include hmul in
/-- **The dimension shifting along the Koszul filtration corresponds under `f`.** -/
public theorem koszulChainIso_pullback (p : ℕ) (hp : p ≤ n) :
    (koszulChainIso E hqc D hn hfree p hp).hom ≫ (bundleComparison f hbase p _).hom ≫
        ((bundlePushforward E' hqc').rightDerived p).map (koszulTermIso f θ lV hu p).hom =
      (bundleComparison f hbase 0 _).hom ≫
        ((bundlePushforward E' hqc').rightDerived 0).map (koszulTermIso f θ lV hu 0).hom ≫
        (koszulChainIso E' hqc' D' hn hfree' p hp).hom := by
  induction p with
  | zero =>
    have e1 := congrArg Iso.hom (koszulChainIso.eq_1 E hqc D hn hfree hp)
    have e2 := congrArg Iso.hom (koszulChainIso.eq_1 E' hqc' D' hn hfree' hp)
    refine (congrArg (· ≫ _) e1).trans ?_
    refine Eq.trans ?_ (congrArg (fun φ => _ ≫ _ ≫ φ) e2).symm
    exact (Category.id_comp _).trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _)).symm
  | succ p ih =>
    have e1 := congrArg Iso.hom (koszulChainIso.eq_2 E hqc D hn hfree p hp)
    have e2 := congrArg Iso.hom (koszulChainIso.eq_2 E' hqc' D' hn hfree' p hp)
    have hs := koszulShiftIso_pullback f θ lV hu hmul hbase hn hfree hfree' hp p
    rw [e1, e2, Iso.trans_hom, Iso.trans_hom]
    exact ladder_comp _ _ _ _ _ _ _ _ _ _ (ih (by lia)) hs

end Koszul

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
