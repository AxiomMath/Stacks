module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Spaces.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum

/-!
# The sum of two effective Cartier divisors is an effective Cartier divisor

Let `X` be an algebraic space over a scheme `S` and let `D₁, D₂ ⊆ X` be effective Cartier
divisors, so that their defining ideal sheaves `𝓘_{D₁}, 𝓘_{D₂} ⊆ 𝒪_X` are invertible
`𝒪_X`-modules.  Following Stacks 083V their sum `D = D₁ + D₂`, the closed subspace
`AlgebraicGeometry.Space.sumClosedSubspaces` of Stacks 083U, is again an effective Cartier
divisor: its defining ideal sheaf is the tensor product `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂}`.

## Main definitions

* `AlgebraicGeometry.Space.idealMulPresheafHom` is the multiplication
  `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝒪_X` of two defining ideal sheaves at the level of presheaves of
  `𝒪_X`-modules, and `AlgebraicGeometry.Space.idealMulToSumPresheaf` is its corestriction to
  `𝓘_{D₁+D₂}`.
* `AlgebraicGeometry.Space.sumIdealHom` is the sheafification of that corestriction, and
  `AlgebraicGeometry.Space.sumIdealIso` is the resulting isomorphism
  `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ≅ 𝓘_{D₁+D₂}`.
* `Stacks.SheafOfModules.monoRange` is the image of a monomorphism of sheaves of modules, as a
  sheaf of submodules of the target, and `Stacks.PresheafOfModules.Submodule.factor` factors a
  morphism of presheaves of modules through a submodule containing its local images.
* `Stacks.SheafOfModules.liftAlongSheafifyIso` extends a morphism into a sheaf of modules along
  a morphism of presheaves whose sheafification is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_sumClosedSubspaces` is **Stacks 083V**.
* `AlgebraicGeometry.Space.sieve_mem_of_forall_isAffine_hom`,
  `AlgebraicGeometry.Space.structureSection_ext_of_forall_isAffine_hom` and
  `AlgebraicGeometry.Space.mem_structureSubmodule_of_forall_isAffine_hom`: a sieve containing
  every affine chart over a fixed surjective chart is covering, so sections of `𝒪_X` and
  membership in a sheaf of ideals of `𝒪_X` are determined on those charts.
* `AlgebraicGeometry.Space.mul_mem_definingIdealAt_sumClosedSubspaces`: the product of the
  defining ideals of `D₁` and `D₂` lies in the defining ideal of their sum.
* `AlgebraicGeometry.Space.mono_definingIdealTensorMul` and
  `AlgebraicGeometry.Space.monoRange_definingIdealTensorMul`: the multiplication
  `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝒪_X` is a monomorphism with image `𝓘_{D₁+D₂}`.

## Implementation notes

The sum of Stacks 083U is formed on a surjective étale scheme chart, and what is known about it
is `AlgebraicGeometry.Space.definingIdealAt_sumClosedSubspaces_of_isAffine`: on an *affine*
étale chart lying over that chart its defining ideal is the product of the two defining ideals.
Everything here is deduced from that one formula, so the covering lemma
`AlgebraicGeometry.Space.sieve_mem_of_forall_isAffine_hom`, which says that those charts cover,
is what makes the two global statements local.

That the multiplication is injective is where invertibility enters: tensoring on the right by
the invertible sheaf `𝓘_{D₂}` is an equivalence, so it carries the inclusion `𝓘_{D₁} ⟶ 𝒪_X` to
a monomorphism — this is `AlgebraicGeometry.Space.definingIdealTensorMul` together with
`AlgebraicGeometry.Space.tensorRightFunctor_map_ι`.  Only `D₂` has to be an effective Cartier
divisor for that; both are needed for Stacks 083V itself, since a tensor product of invertible
sheaves is invertible.

Monomorphism and isomorphism hypotheses are passed as explicit arguments throughout rather
than left to instance search: the ambient category of `𝒪_X`-modules is presented by two terms
which are definitionally but not syntactically equal — `structureRingSheaf` and the
`structureSheaf` of the tensor-sheafification API — and instance search does not unify them.

## References

* [Stacks Project, Tag 083V](https://stacks.math.columbia.edu/tag/083V)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open Stacks.PresheafOfModules.TensorInternalHom
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules.TensorSheafification (sheafify toSheafify sheafifyAdjunction)

namespace CategoryTheory

universe u v

/-- A composite of two monomorphisms is a monomorphism.  The two hypotheses are explicit
arguments, so that the statement applies to a category presented by a term which instance
search does not unify with the one carrying the monomorphism instances. -/
theorem mono_comp_of_mono {C : Type u} [Category.{v} C] {Z Y W : C} (f : Z ⟶ Y) (g : Y ⟶ W)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

/-- The forward morphism of an isomorphism is a monomorphism, with the isomorphism as an
explicit argument. -/
theorem mono_hom_of_iso {C : Type u} [Category.{v} C] {Z Y : C} (e : Z ≅ Y) : Mono e.hom := by
  have := Iso.isIso_hom e
  infer_instance

/-- An equivalence of categories carries monomorphisms to monomorphisms, with the monomorphism
hypothesis as an explicit argument. -/
theorem Equivalence.mono_functor_map_of_mono {C D : Type u} [Category.{v} C] [Category.{v} D]
    (e : C ≌ D) {A Y : C} (f : A ⟶ Y) (hf : Mono f) : Mono (e.functor.map f) := by
  have := hf
  exact e.mono_functor_map f

end CategoryTheory

namespace Stacks.PresheafOfModules.Submodule

universe u v w

/-- **A morphism of presheaves of modules whose local images lie in a submodule factors through
it.** -/
noncomputable def factor {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    {P M : _root_.PresheafOfModules.{w} R} (N : M.Submodule) (f : P ⟶ M)
    (hf : ∀ (U : Cᵒᵖ) (x : P.obj U), f.app U x ∈ N.obj U) :
    P ⟶ N.toPresheafOfModules where
  app U := ModuleCat.ofHom (LinearMap.codRestrict (N.obj U) (f.app U).hom (hf U))
  naturality {U V} g := by
    ext x
    exact Subtype.ext (_root_.PresheafOfModules.naturality_apply f g x)

/-- The factorisation of `Stacks.PresheafOfModules.Submodule.factor` recovers the original
morphism after the inclusion of the submodule. -/
theorem factor_ι {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    {P M : _root_.PresheafOfModules.{w} R} (N : M.Submodule) (f : P ⟶ M)
    (hf : ∀ (U : Cᵒᵖ) (x : P.obj U), f.app U x ∈ N.obj U) :
    factor N f hf ≫ N.ι = f := rfl

end Stacks.PresheafOfModules.Submodule

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {F G : _root_.SheafOfModules.{w} R} (f : F ⟶ G) (hf : Mono f)

/-- **The image of a monomorphism of sheaves of modules**, as a sheaf of submodules of the
target: the sectionwise ranges are a submodule, and they are a sheaf because the source is one
and the monomorphism identifies it with its range. -/
noncomputable def monoRange : G.Submodule where
  obj U := LinearMap.range (f.val.app U).hom
  map {U V} g := by
    rintro _ ⟨x, rfl⟩
    exact ⟨F.val.map g x, _root_.PresheafOfModules.naturality_apply f.val g x⟩
  isSheaf := by
    have := hf
    let ft := Functor.whiskerRight ((_root_.SheafOfModules.toSheaf R).map f).hom
      (forget AddCommGrpCat)
    have hmv : Mono f.val := (_root_.SheafOfModules.forget R).map_mono f
    have hmono : Mono ft := by
      have : ∀ U, Mono (ft.app U) := fun U =>
        (CategoryTheory.mono_iff_injective (ft.app U)).mpr
          (_root_.PresheafOfModules.injective_of_mono f.val U)
      exact NatTrans.mono_of_mono_app ft
    have hsh (M : _root_.SheafOfModules.{w} R) :
        Presieve.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat) := by
      rw [← isSheaf_iff_isSheaf_of_type]
      exact GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf
    exact ((Subfunctor.range ft).isSheaf_iff (hsh G)).mp
      (Presieve.isSheaf_iso J (asIso (Subfunctor.toRange ft)) (hsh F))

/-- A monomorphism of sheaves of modules is an isomorphism onto its image. -/
noncomputable def monoRangeIso : F ≅ (monoRange f hf).toSheafOfModules := by
  have := hf
  have : Mono f.val := (_root_.SheafOfModules.forget R).map_mono f
  refine (_root_.SheafOfModules.fullyFaithfulForget R).preimageIso ?_
  refine _root_.PresheafOfModules.isoMk (fun U =>
    (LinearEquiv.ofInjective (f.val.app U).hom
      (_root_.PresheafOfModules.injective_of_mono f.val U)).toModuleIso) ?_
  intro U V g
  ext x
  exact Subtype.ext (_root_.PresheafOfModules.naturality_apply f.val g x)

/-- The isomorphism of a monomorphism with its image is compatible with the inclusion of the
image. -/
theorem monoRangeIso_hom_ι : (monoRangeIso f hf).hom ≫ (monoRange f hf).ι = f := by
  ext U x
  rfl

/-- The image of a monomorphism is contained in any sheaf of submodules through which the
monomorphism factors. -/
theorem monoRange_le (N : G.Submodule) (l : F ⟶ N.toSheafOfModules) (hl : l ≫ N.ι = f) :
    monoRange f hf ≤ N := by
  intro U y hy
  obtain ⟨x, rfl⟩ := hy
  have h := congrArg (fun g : F ⟶ G => g.val.app U x) hl
  rw [← h]
  exact (l.val.app U x).property

/-- Transport along an equality of sheaves of submodules is compatible with their
inclusions. -/
theorem submodule_eqToIso_hom_ι {M : _root_.SheafOfModules.{w} R} {I N : M.Submodule}
    (h : I = N) :
    (eqToIso (congrArg _root_.SheafOfModules.Submodule.toSheafOfModules h)).hom ≫ N.ι = I.ι := by
  subst h
  simp

/-- The underlying morphism of presheaves of modules of an isomorphism of sheaves of modules is
an isomorphism. -/
theorem isIso_val_of_iso {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N) :
    IsIso e.hom.val :=
  ((_root_.SheafOfModules.forget R).mapIso e).isIso_hom

section Sheafify

open Stacks.SheafOfModules.TensorSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafification carries an isomorphism of presheaves of modules to an isomorphism. -/
theorem isIso_sheafify_map_of_isIso {P Q : _root_.PresheafOfModules.{w} (structureSheaf O hO).obj}
    (f : P ⟶ Q) (hf : IsIso f) : IsIso ((sheafify O hO).map f) := by
  have := hf
  infer_instance

/-- **Extension along a morphism whose sheafification is an isomorphism.** A morphism from `P`
into a sheaf of modules extends uniquely over any `f : P ⟶ Q` whose sheafification is an
isomorphism, because morphisms into a sheaf factor through the sheafification. -/
noncomputable def liftAlongSheafifyIso
    {P Q : _root_.PresheafOfModules.{w} (structureSheaf O hO).obj}
    (f : P ⟶ Q) (hf : IsIso ((sheafify O hO).map f))
    (N : _root_.SheafOfModules.{w} (structureSheaf O hO)) (φ : P ⟶ N.val) : Q ⟶ N.val :=
  haveI := hf
  (sheafifyAdjunction O hO).homEquiv Q N
    (inv ((sheafify O hO).map f) ≫ ((sheafifyAdjunction O hO).homEquiv P N).symm φ)

/-- The extension of `Stacks.SheafOfModules.liftAlongSheafifyIso` restricts to the given
morphism. -/
theorem comp_liftAlongSheafifyIso
    {P Q : _root_.PresheafOfModules.{w} (structureSheaf O hO).obj}
    (f : P ⟶ Q) (hf : IsIso ((sheafify O hO).map f))
    (N : _root_.SheafOfModules.{w} (structureSheaf O hO)) (φ : P ⟶ N.val) :
    f ≫ liftAlongSheafifyIso O hO f hf N φ = φ := by
  have := hf
  refine Eq.trans ((sheafifyAdjunction O hO).homEquiv_naturality_left f
    (inv ((sheafify O hO).map f) ≫
      ((sheafifyAdjunction O hO).homEquiv P N).symm φ)).symm ?_
  refine Eq.trans (congrArg ((sheafifyAdjunction O hO).homEquiv P N)
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun z => z ≫ ((sheafifyAdjunction O hO).homEquiv P N).symm φ)
        (IsIso.hom_inv_id ((sheafify O hO).map f))) (Category.id_comp _)))) ?_
  exact ((sheafifyAdjunction O hO).homEquiv P N).apply_symm_apply φ

/-- The sheafification of the extension of `Stacks.SheafOfModules.liftAlongSheafifyIso` is an
isomorphism as soon as the sheafification of the morphism being extended is. -/
theorem isIso_sheafify_map_liftAlongSheafifyIso
    {P Q : _root_.PresheafOfModules.{w} (structureSheaf O hO).obj}
    (f : P ⟶ Q) (hf : IsIso ((sheafify O hO).map f))
    (N : _root_.SheafOfModules.{w} (structureSheaf O hO)) (φ : P ⟶ N.val)
    (hφ : IsIso ((sheafify O hO).map φ)) :
    IsIso ((sheafify O hO).map (liftAlongSheafifyIso O hO f hf N φ)) := by
  have h : (sheafify O hO).map f ≫
      (sheafify O hO).map (liftAlongSheafifyIso O hO f hf N φ) = (sheafify O hO).map φ := by
    rw [← Functor.map_comp, comp_liftAlongSheafifyIso]
  have := hf
  have : IsIso ((sheafify O hO).map f ≫
      (sheafify O hO).map (liftAlongSheafifyIso O hO f hf N φ)) := h ▸ hφ
  exact IsIso.of_isIso_comp_left ((sheafify O hO).map f)
    ((sheafify O hO).map (liftAlongSheafifyIso O hO f hf N φ))

/-- The unit of sheafification followed by the underlying morphism of the sheafified extension of
`φ` is `φ`. -/
private theorem toSheafify_comp_homEquiv_symm_val
    {P : _root_.PresheafOfModules.{w} (structureSheaf O hO).obj}
    {N : _root_.SheafOfModules.{w} (structureSheaf O hO)} (φ : P ⟶ N.val) :
    toSheafify O hO P ≫ (((sheafifyAdjunction O hO).homEquiv P N).symm φ).val = φ :=
  ((sheafifyAdjunction O hO).homEquiv P N).apply_symm_apply φ

/-- A morphism from a sheafification into a sheaf of modules whose own sheafification is an
isomorphism is an isomorphism: it is the sheafification of its restriction along the unit,
followed by the counit of sheafification. -/
theorem isIso_of_isIso_sheafify_map_homEquiv
    {P : _root_.PresheafOfModules.{w} (structureSheaf O hO).obj}
    {N : _root_.SheafOfModules.{w} (structureSheaf O hO)} (φ : P ⟶ N.val)
    (hφ : IsIso ((sheafify O hO).map φ)) :
    IsIso (((sheafifyAdjunction O hO).homEquiv P N).symm φ) := by
  have h : ((sheafifyAdjunction O hO).homEquiv P N).symm φ =
      (sheafify O hO).map φ ≫ (sheafifyAdjunction O hO).counit.app N :=
    Adjunction.homEquiv_symm_apply (sheafifyAdjunction O hO) P N φ
  have hcounit : IsIso ((sheafifyAdjunction O hO).counit.app N) := by
    have : IsIso (sheafifyAdjunction O hO).counit := by
      show IsIso (_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheaf O hO).obj)).counit
      infer_instance
    exact NatIso.isIso_app_of_isIso _ _
  rw [h]
  exact IsIso.comp_isIso' hφ hcounit

end Sheafify

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### Affine charts over the chart on which the sum is formed -/

/-- The étale chart of `X` on which `AlgebraicGeometry.Space.sumClosedSubspaces` is formed, as
an object of the small étale site. -/
abbrev sumAtlasChart : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk (atlasHom B S hS X), atlasHom_etale B S hS X⟩

/-- The chart `AlgebraicGeometry.Space.sumAtlasChart` is surjective on points. -/
theorem sumAtlasChart_isSurjective : IsSurjective B S hS (sumAtlasChart B S hS X).1.hom :=
  (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 _
    (atlasHom B S hS X)).1 (atlasHom_surjective B S hS X)

/-- **A sieve containing every affine chart over a fixed surjective chart is covering.** Every
étale chart `U` of `X` is covered by the single chart `U ×_X Uc`, which lies over `Uc`, and that
chart is in turn covered by affine charts over it; an affine chart over `U ×_X Uc` lies over
both `U` and `Uc`. -/
theorem sieve_mem_of_forall_isAffine_hom (Uc : SmallEtale B S hS X.1)
    (hsurj : IsSurjective B S hS Uc.1.hom) (U : SmallEtale B S hS X.1)
    (T : Sieve U)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ Uc) → ∀ k : A ⟶ U, T k) :
    T ∈ SmallEtale.topology B S hS X.1 U := by
  have : (AffineEtale.inclusion B S hS X.1).IsCoverDense
      (SmallEtale.topology B S hS X.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2.isCoverDense'
  refine (SmallEtale.topology B S hS X.1).transitive
    (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 Uc hsurj U) _ ?_
  rintro Y f ⟨i, ⟨m⟩⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    ((AffineEtale.inclusion B S hS X.1).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS X.1) Y)
  rintro Z g ⟨A, l, k, ⟨rfl⟩⟩
  show T ((l ≫ k) ≫ f)
  simpa only [Category.assoc] using T.downward_closed (h _ A.property (k ≫ m) (k ≫ f)) l

/-- **Sections of `𝒪_X` are determined on the affine charts lying over a fixed surjective
chart.** -/
theorem structureSection_ext_of_forall_isAffine_hom (Uc : SmallEtale B S hS X.1)
    (hsurj : IsSurjective B S hS Uc.1.hom) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (s t : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ Uc) → ∀ k : A ⟶ U.unop,
        ((structureRingSheaf B S hS X).obj.map k.op).hom s =
          ((structureRingSheaf B S hS X).obj.map k.op).hom t) :
    s = t := by
  let T : Sieve U.unop :=
    { arrows := fun Z k => ((structureRingSheaf B S hS X).obj.map k.op).hom s =
        ((structureRingSheaf B S hS X).obj.map k.op).hom t
      downward_closed := fun {Z W} {k} hk l => by
        have e (x) : ((structureRingSheaf B S hS X).obj.map (l ≫ k).op).hom x =
            ((structureRingSheaf B S hS X).obj.map l.op).hom
              (((structureRingSheaf B S hS X).obj.map k.op).hom x) := by
          rw [op_comp, Functor.map_comp]
          rfl
        rw [e, e, hk] }
  exact (structureRingSheaf B S hS X).property.isSeparated U.unop T
    (sieve_mem_of_forall_isAffine_hom B S hS X Uc hsurj U.unop T h) s t fun Z k hk => hk

/-- **Membership in a sheaf of ideals of `𝒪_X` is checked on the affine charts lying over a
fixed surjective chart.** -/
theorem mem_structureSubmodule_of_forall_isAffine_hom (Uc : SmallEtale B S hS X.1)
    (hsurj : IsSurjective B S hS Uc.1.hom)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (s : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ Uc) → ∀ k : A ⟶ U.unop,
        ((structureRingSheaf B S hS X).obj.map k.op).hom s ∈ N.obj (op A)) :
    s ∈ N.obj U :=
  N.isSheaf s (sieve_mem_of_forall_isAffine_hom B S hS X Uc hsurj U.unop _ h)

/-! ### The multiplication of two defining ideal sheaves, at the level of presheaves -/

section Multiplication

/-- A local section of the structure sheaf of `X`, regarded as a module over itself: the module
of sections of `𝒪_X` and its spelling through `AlgebraicGeometry.Space.modulePresheaf` have the
same carrier and differ only in how they are indexed. -/
def unitSectionOf {U : (SmallEtale B S hS X.1)ᵒᵖ}
    (z : (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))).obj U) :
    ToType ((structureRingSheaf B S hS X).obj.obj U) := z

/-- `AlgebraicGeometry.Space.unitSectionOf` sends the zero section to zero. -/
@[simp]
theorem unitSectionOf_zero {U : (SmallEtale B S hS X.1)ᵒᵖ} :
    unitSectionOf B S hS X
      (0 : (modulePresheaf B S hS X
        (SheafOfModules.unit (structureRingSheaf B S hS X))).obj U) = 0 :=
  rfl

/-- `AlgebraicGeometry.Space.unitSectionOf` is additive. -/
@[simp]
theorem unitSectionOf_add {U : (SmallEtale B S hS X.1)ᵒᵖ}
    (z z' : (modulePresheaf B S hS X
      (SheafOfModules.unit (structureRingSheaf B S hS X))).obj U) :
    unitSectionOf B S hS X (z + z') =
      unitSectionOf B S hS X z + unitSectionOf B S hS X z' :=
  rfl

/-- The ring of sections of `𝒪_X` over an étale chart is commutative. -/
theorem unitSection_mul_comm {U : (SmallEtale B S hS X.1)ᵒᵖ}
    (a b : ToType ((structureRingSheaf B S hS X).obj.obj U)) : a * b = b * a :=
  mul_comm (G := ToType ((structureCommRings B S hS X).obj U)) a b

variable (D₁ D₂ : ClosedSubspaces B S hS X.1)

/-- The multiplication `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝒪_X` of the defining ideal sheaves of two
closed subspaces, at the level of presheaves of `𝒪_X`-modules: tensor the inclusion of
`𝓘_{D₁}` with `𝓘_{D₂}`, undo the unit constraint, and include `𝓘_{D₂}`. -/
def idealMulPresheafHom :
    modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁) ⊗
        modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂) ⟶
      modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  (valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (definingIdealSheaf B S hS X D₁).ι ⊗ₘ
      𝟙 (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂))) ≫
    (λ_ (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂))).hom ≫
      valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (definingIdealSheaf B S hS X D₂).ι

/-- The presheaf-level multiplication of defining ideal sheaves sends a pure tensor of local
sections to their product. -/
theorem idealMulPresheafHom_app_tmul (U : (SmallEtale B S hS X.1)ᵒᵖ)
    {a b : ToType ((structureRingSheaf B S hS X).obj.obj U)}
    (ha : a ∈ definingIdealAt B S hS X D₁ U) (hb : b ∈ definingIdealAt B S hS X D₂ U) :
    (show ToType ((structureRingSheaf B S hS X).obj.obj U) from
        ((idealMulPresheafHom B S hS X D₁ D₂).app U).hom
          ((⟨a, ha⟩ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁)).obj U) ⊗ₜ
            (⟨b, hb⟩ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)).obj U))) =
      a * b :=
  rfl

/-- **The product of the defining ideals of `D₁` and `D₂` lies in the defining ideal of their
sum.** On an affine chart over the chart on which the sum is formed the two agree, and both
membership and the formula are local on the small étale site. -/
theorem mul_mem_definingIdealAt_sumClosedSubspaces (U : (SmallEtale B S hS X.1)ᵒᵖ)
    {a b : ToType ((structureRingSheaf B S hS X).obj.obj U)}
    (ha : a ∈ definingIdealAt B S hS X D₁ U) (hb : b ∈ definingIdealAt B S hS X D₂ U) :
    a * b ∈ definingIdealAt B S hS X (sumClosedSubspaces B S hS X D₁ D₂) U := by
  refine mem_structureSubmodule_of_forall_isAffine_hom B S hS X (sumAtlasChart B S hS X)
    (sumAtlasChart_isSurjective B S hS X)
    (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)) U _
    fun A hA m k => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  rw [definingIdealSheaf_obj, definingIdealAt_sumClosedSubspaces_of_isAffine B S hS X D₁ D₂ A m,
    map_mul]
  exact Ideal.mul_mem_mul (definingIdealAt_map B S hS X D₁ k.op a ha)
    (definingIdealAt_map B S hS X D₂ k.op b hb)

/-- Every local section in the image of the presheaf-level multiplication lies in the defining
ideal of the sum. -/
theorem idealMulPresheafHom_mem (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁) ⊗
      modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)).obj U) :
    unitSectionOf B S hS X (((idealMulPresheafHom B S hS X D₁ D₂).app U).hom z) ∈
      definingIdealAt B S hS X (sumClosedSubspaces B S hS X D₁ D₂) U := by
  refine TensorProduct.inductionOn (motive := fun z => unitSectionOf B S hS X
      (((idealMulPresheafHom B S hS X D₁ D₂).app U).hom z) ∈
      definingIdealAt B S hS X (sumClosedSubspaces B S hS X D₁ D₂) U) z
    (fun x y => ?_) (fun w w' hw hw' => ?_)
  · exact mul_mem_definingIdealAt_sumClosedSubspaces B S hS X D₁ D₂ U x.2 y.2
  · exact cast (congrArg
      (fun v => unitSectionOf B S hS X v ∈
        definingIdealAt B S hS X (sumClosedSubspaces B S hS X D₁ D₂) U)
      (map_add ((idealMulPresheafHom B S hS X D₁ D₂).app U).hom w w').symm)
      (Submodule.add_mem _ hw hw')

/-! ### The multiplication as a morphism of sheaves -/

/-- The multiplication `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝓘_{D₁+D₂}` of the defining ideal sheaves of two
closed subspaces into the defining ideal sheaf of their sum, at the level of presheaves of
`𝒪_X`-modules. -/
def idealMulToSumPresheaf :
    modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁) ⊗
        modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂) ⟶
      modulePresheaf B S hS X
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)) :=
  Stacks.PresheafOfModules.Submodule.factor
    (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).toSubmodule
    (idealMulPresheafHom B S hS X D₁ D₂)
    fun U x => idealMulPresheafHom_mem B S hS X D₁ D₂ U x

/-- Following the presheaf-level multiplication into `𝓘_{D₁+D₂}` by the inclusion of that ideal
sheaf gives back the multiplication into `𝒪_X`. -/
theorem idealMulToSumPresheaf_comp_ι :
    idealMulToSumPresheaf B S hS X D₁ D₂ ≫
        valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι =
      idealMulPresheafHom B S hS X D₁ D₂ :=
  rfl

/-- The multiplication `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝓘_{D₁+D₂}` of defining ideal sheaves, as a
morphism of sheaves of `𝒪_X`-modules: the morphism adjoint to the presheaf-level multiplication
under sheafification. -/
def sumIdealHom :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
            ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
            ((structureRingSheaf B S hS X).property)⟩).obj
          ((idealSheafOfModules B S hS X D₁))).obj ((idealSheafOfModules B S hS X D₂))) ⟶
      idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂) :=
  ((sheafifyAdjunction (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property).homEquiv _ _).symm
      (idealMulToSumPresheaf B S hS X D₁ D₂)

/-- Restricting the sheafified multiplication along the unit of sheafification gives back the
presheaf-level multiplication. -/
theorem toSheafify_comp_sumIdealHom :
    toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁) ⊗
          modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)) ≫
      (sumIdealHom B S hS X D₁ D₂).val = idealMulToSumPresheaf B S hS X D₁ D₂ :=
  Stacks.SheafOfModules.toSheafify_comp_homEquiv_symm_val _ _ _

end Multiplication

set_option maxHeartbeats 1000000 in
/-- Restricting the left unit constraint of the sheaf tensor product along the unit of
sheafification gives back the left unit constraint of the tensor product of presheaves. -/
theorem toSheafify_comp_tensorProductLeftUnitor
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) :
    toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) ⊗
          modulePresheaf B S hS X M) ≫
      (tensorProductLeftUnitor (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property M).hom.val =
      (λ_ (modulePresheaf B S hS X M)).hom := by
  have h : (tensorProductLeftUnitor (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M).hom =
      ((sheafifyAdjunction (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property).homEquiv _ M).symm
          (λ_ (modulePresheaf B S hS X M)).hom :=
    (Adjunction.homEquiv_symm_apply (sheafifyAdjunction (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property) _ M
        (λ_ (modulePresheaf B S hS X M)).hom).symm
  rw [h]
  exact Stacks.SheafOfModules.toSheafify_comp_homEquiv_symm_val (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property (N := M) (λ_ (modulePresheaf B S hS X M)).hom

section Comparison

variable (D₁ D₂ : ClosedSubspaces B S hS X.1)

/-- Restricting `AlgebraicGeometry.Space.definingIdealTensorMul` along the unit of sheafification
gives the presheaf-level multiplication of the two defining ideal sheaves. -/
theorem toSheafify_comp_definingIdealTensorMul :
    toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁) ⊗
          modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)) ≫
      (definingIdealTensorMul B S hS X D₁ D₂).val =
      idealMulPresheafHom B S hS X D₁ D₂ := by
  have h1 := ((sheafifyAdjunction (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property).unit.naturality
      (show (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁) ⊗
            modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)) ⟶
          (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) ⊗
            modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)) from
        valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
            (definingIdealSheaf B S hS X D₁).ι ⊗ₘ
          𝟙 (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)))).symm
  have h2 := toSheafify_comp_tensorProductLeftUnitor B S hS X
    (idealSheafOfModules B S hS X D₂)
  refine Eq.trans (Eq.trans (Category.assoc _ _ _).symm
    (congrArg (fun z => z ≫ ((tensorProductLeftUnitor (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D₂)).hom ≫
      (definingIdealSheaf B S hS X D₂).ι).val) h1)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z => (valPresheafMap (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (definingIdealSheaf B S hS X D₁).ι ⊗ₘ
    𝟙 (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂))) ≫ z) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z => z ≫ valPresheafMap (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property (definingIdealSheaf B S hS X D₂).ι) h2

/-- Following the sheafified multiplication of the two defining ideal sheaves by the inclusion
of the defining ideal sheaf of the sum gives `definingIdealTensorMul`. -/
theorem sumIdealHom_comp_ι :
    sumIdealHom B S hS X D₁ D₂ ≫
        (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι =
      definingIdealTensorMul B S hS X D₁ D₂ := by
  refine hom_ext_of_toSheafify B S hS X
    (Eq.trans ?_ (toSheafify_comp_definingIdealTensorMul B S hS X D₁ D₂).symm)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ valPresheafMap (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property
      (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι)
    (toSheafify_comp_sumIdealHom B S hS X D₁ D₂)) ?_
  exact idealMulToSumPresheaf_comp_ι B S hS X D₁ D₂

/-- **The multiplication `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝒪_X` is a monomorphism** when `D₂` is an
effective Cartier divisor: tensoring on the right by the invertible sheaf `𝓘_{D₂}` is an
equivalence, hence carries the inclusion `𝓘_{D₁} ⟶ 𝒪_X` to a monomorphism, and the remaining
two factors are an isomorphism and the inclusion of a sheaf submodule. -/
theorem mono_definingIdealTensorMul (hD₂ : IsEffectiveCartierDivisor B S hS X D₂) :
    Mono (definingIdealTensorMul B S hS X D₁ D₂) := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D₂) := hD₂
  have heq : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
        (structureRingSheaf B S hS X).property⟩).flip.obj
      (idealSheafOfModules B S hS X D₂)).IsEquivalence :=
    Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence
      (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      (idealSheafOfModules B S hS X D₂)
  have hmi₁ : Mono (definingIdealSheaf B S hS X D₁).ι := inferInstance
  have hmi₂ : Mono (definingIdealSheaf B S hS X D₂).ι := inferInstance
  have h1 : Mono ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
        (structureRingSheaf B S hS X).property⟩).map (definingIdealSheaf B S hS X D₁).ι).app
      (idealSheafOfModules B S hS X D₂))) := by
    rw [← tensorRightFunctor_map_ι B S hS X D₁ D₂]
    exact Equivalence.mono_functor_map_of_mono
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩).flip.obj
        (idealSheafOfModules B S hS X D₂)).asEquivalence
      (definingIdealSheaf B S hS X D₁).ι hmi₁
  exact mono_comp_of_mono _ _ h1
    (mono_comp_of_mono _ _ (mono_hom_of_iso _) hmi₂)

/-- **The image of the multiplication of the two defining ideal sheaves is the defining ideal
sheaf of the sum.** One inclusion is the factorisation through `𝓘_{D₁+D₂}`; the other holds
because on an affine chart over the chart on which the sum is formed the defining ideal of the
sum is the product of the two defining ideals, and every product of local sections is the image
of their pure tensor. -/
theorem monoRange_definingIdealTensorMul (hD₂ : IsEffectiveCartierDivisor B S hS X D₂) :
    (Stacks.SheafOfModules.monoRange (definingIdealTensorMul B S hS X D₁ D₂)
          (mono_definingIdealTensorMul B S hS X D₁ D₂ hD₂) :
        (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) =
      definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂) := by
  refine le_antisymm (Stacks.SheafOfModules.monoRange_le _ _ _ (sumIdealHom B S hS X D₁ D₂)
    (sumIdealHom_comp_ι B S hS X D₁ D₂)) ?_
  refine structureSubmodule_le_of_forall_isAffine_hom B S hS X (sumAtlasChart B S hS X)
    (sumAtlasChart_isSurjective B S hS X) _ _ fun A hA mA => ?_
  have hAff : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  refine le_of_eq_of_le
    (definingIdealAt_sumClosedSubspaces_of_isAffine B S hS X D₁ D₂ A mA) ?_
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  exact ⟨_, congrArg (fun φ => (φ.app (op A)).hom
      ((⟨a, ha⟩ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁)).obj (op A)) ⊗ₜ
        (⟨b, hb⟩ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)).obj (op A))))
    (toSheafify_comp_definingIdealTensorMul B S hS X D₁ D₂)⟩

/-- **The multiplication `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝓘_{D₁+D₂}` is an isomorphism** when `D₂` is
an effective Cartier divisor.  It agrees, after the monomorphism `𝓘_{D₁+D₂} ⟶ 𝒪_X`, with the
isomorphism of `definingIdealTensorMul` onto its image, which is `𝓘_{D₁+D₂}`. -/
theorem isIso_sumIdealHom (hD₂ : IsEffectiveCartierDivisor B S hS X D₂) :
    IsIso (sumIdealHom B S hS X D₁ D₂) := by
  have hmono := mono_definingIdealTensorMul B S hS X D₁ D₂ hD₂
  have hN := monoRange_definingIdealTensorMul B S hS X D₁ D₂ hD₂
  have hmi : Mono (definingIdealSheaf B S hS X
    (sumClosedSubspaces B S hS X D₁ D₂)).ι := inferInstance
  have h1 : ((Stacks.SheafOfModules.monoRangeIso
        (definingIdealTensorMul B S hS X D₁ D₂) hmono).hom ≫
      (eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules hN)).hom) ≫
      (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι =
      definingIdealTensorMul B S hS X D₁ D₂ := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z => (Stacks.SheafOfModules.monoRangeIso
        (definingIdealTensorMul B S hS X D₁ D₂) hmono).hom ≫ z)
      (Stacks.SheafOfModules.submodule_eqToIso_hom_ι hN)) ?_
    exact Stacks.SheafOfModules.monoRangeIso_hom_ι _ hmono
  have key := (cancel_mono (definingIdealSheaf B S hS X
    (sumClosedSubspaces B S hS X D₁ D₂)).ι).1
      ((sumIdealHom_comp_ι B S hS X D₁ D₂).trans h1.symm)
  rw [key]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (Iso.isIso_hom _)

/-- **The multiplication `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ≅ 𝓘_{D₁+D₂}`**, for `D₂` an effective Cartier
divisor: the defining ideal sheaf of a sum of closed subspaces is the tensor product of the
defining ideal sheaves of the summands. -/
def sumIdealIso (hD₂ : IsEffectiveCartierDivisor B S hS X D₂) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
            ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
            ((structureRingSheaf B S hS X).property)⟩).obj
          ((idealSheafOfModules B S hS X D₁))).obj ((idealSheafOfModules B S hS X D₂))) ≅
      idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂) :=
  haveI := isIso_sumIdealHom B S hS X D₁ D₂ hD₂
  asIso (sumIdealHom B S hS X D₁ D₂)

/-- **Stacks 083V.** The sum of two effective Cartier divisors on an algebraic space is again an
effective Cartier divisor: its defining ideal sheaf is the tensor product of the defining ideal
sheaves of the summands, and a tensor product of invertible sheaves is invertible. -/
@[stacks 083V]
theorem isEffectiveCartierDivisor_sumClosedSubspaces
    (hD₁ : IsEffectiveCartierDivisor B S hS X D₁)
    (hD₂ : IsEffectiveCartierDivisor B S hS X D₂) :
    IsEffectiveCartierDivisor B S hS X (sumClosedSubspaces B S hS X D₁ D₂) := by
  have h₁ : Stacks.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D₁) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hD₁
  have h₂ : Stacks.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D₂) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hD₂
  have ht : Stacks.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
          ((structureRingSheaf B S hS X).property)⟩).obj
        ((idealSheafOfModules B S hS X D₁))).obj ((idealSheafOfModules B S hS X D₂)))) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property _ _
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_of_iso (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (sumIdealIso B S hS X D₁ D₂ hD₂))

end Comparison

end AlgebraicGeometry.Space

end
