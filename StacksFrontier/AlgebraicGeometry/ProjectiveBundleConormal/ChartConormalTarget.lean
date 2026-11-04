module

public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.LocalityGenerator
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineZeroSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartSourceTilde
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartZeroSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ZeroSectionGenerator
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The target of the conormal map of Tag 0B3V clause 3, over a chart

Over a chart `W`, the conormal sheaf `𝒞_σ` of the section in [Stacks, Tag 0B3V] clause 3 — the
target of the conormal map of that clause — is the quasi-coherent sheaf `(ker p)^~` attached to
the kernel of the chart's linear form, pulled back along `W ≅ Spec Γ(X, W)`. On the chart, `σ`
factors as

  `W ≅ Spec Γ(X, W) --zero section--> 𝐀(ker p) --open immersion--> π⁻¹W ⊆ 𝐏(ℰ)`,

and the conormal sheaf of a morphism does not change when an open immersion is cancelled off its
target, nor — up to pullback — when an isomorphism is cancelled off its source.

## Main definitions

* `Stacks.Conormal.restrictConormalIsoOfOpenFactor`: **the general statement.** For an immersion
  `i : Z ⟶ Y`, an open `V` of `Y` whose preimage is `W`, and a factorization of `i|_W` as an
  isomorphism `α` followed by a morphism `g` followed by an open immersion into `V`, the
  restriction of `𝒞_i` to `W` is `α^* g^* ℐ(g)`.
* `Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTilde`: **the target of clause 3's
  conormal map, restricted to a chart, is `(ker p)^~`** — the companion of
  `Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde`.

## Main results

* `Stacks.Conormal.restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap`: **the
  generator formula for that identification**, read on the conormal generator of [Stacks,
  Tag 01R3] attached to a section of `ℐ_i` over `V`.
* `Stacks.ProjectiveBundleConormal.isoSpec_comp_zeroSection_comp_splitChart_comp_ι`: the
  factorization of `σ|_W` through the zero section of the affine bundle, composed with the
  inclusion of `π⁻¹W`.
* `restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`: **the target half of the
  chart computation of clause 3, on a generator.** When the morphism `g` of the factorization is
  the zero section of an affine bundle, the identification composed with
  `Stacks.ProjectiveBundleConormal.conormalZeroSectionIso` carries the conormal generator named by
  a section of `ℐ_i` over `V` to the canonical global section of `K^~` named by the derivative at
  the origin of the corresponding element of the augmentation ideal.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.Conormal

/-- An endomorphism in a preorder acts trivially on a presheaf of modules. -/
private theorem map_self_apply {C : Type*} [Preorder C] {R : Cᵒᵖ ⥤ RingCat}
    (M : PresheafOfModules R) {X : Cᵒᵖ} (f : X ⟶ X) (t : M.obj X) : M.map f t = t :=
  (PresheafOfModules.congr_map_apply (M := M) (Subsingleton.elim f (𝟙 X)) t).trans
    (congrArg (fun φ => ModuleCat.Hom.hom φ t) (M.map_id X))

/-- **The conormal sheaf of an immersion, restricted to the preimage of an open of the ambient
scheme over which the immersion factors through an affine bundle.** Let `i : Z ⟶ Y` be an
immersion, `V` an open of `Y`, and `W` the preimage `i ⁻¹ᵁ V`. Suppose the restriction of `i` to
`W` factors as an isomorphism `α : W ≅ S`, then a morphism `g : S ⟶ T`, then an open immersion
`j : T ⟶ V`. Then

  `𝒞_i|_W ≅ α^* g^* ℐ(g)`. -/
@[sga "6 VII 1.6" "partial"]
def restrictConormalIsoOfOpenFactor {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsImmersion i]
    (V : Y.Opens) {W : Z.Opens} (hW : W = i ⁻¹ᵁ V) {S T : Scheme.{u}} (α : W.toScheme ≅ S)
    (g : S ⟶ T) (j : T ⟶ V.toScheme) [IsOpenImmersion j]
    (hfac : α.hom ≫ g ≫ j ≫ V.ι = W.ι ≫ i) :
    (Scheme.Modules.restrictFunctor W.ι).obj (Stacks.Conormal.conormalSheaf i) ≅
      (Scheme.Modules.pullback α.hom).obj
        ((Scheme.Modules.pullback g).obj
          (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom)) := by
  subst hW
  refine (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapIso
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i) ≪≫
      Stacks.Conormal.Locality.conormalRestrictIso i V ≪≫
      Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) j (i ∣_ V) ?_ ≪≫
      Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource α g
  refine (cancel_mono V.ι).mp ?_
  exact (Category.assoc _ _ _).trans
    ((Category.assoc _ _ _).trans (hfac.trans (morphismRestrict_ι i V).symm))

/-- **The generator formula for `Stacks.Conormal.restrictConormalIsoOfOpenFactor`.** The
identification carries the conormal generator of `𝒞_i|_W` named by a section `y` of `ℐ_i` over
`V` — that is, `Stacks.Immersion.canonicalConormalQuotientMap` of `y`, restricted — to the
iterated unit generator of `α^* g^* ℐ_g` named by the section `x` of `ℐ_{α ≫ g}` that corresponds
to `y`, read through `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource`.

The morphism `L`, with `hL : (α.hom ≫ g) ≫ j = L`, stands for `i ∣_ V`; the opens `U` of `W` and
`P` of `T`, with `hU : U = W.ι ⁻¹ᵁ W` and `hP : P = j ⁻¹ᵁ (V.ι ⁻¹ᵁ V)`, are arbitrary opens equal
to those preimages; the section `y'` of `ℐ_L` corresponding to `y` is pinned by `hy'` through its
image in the structure sheaf; and `ν`, `ρ` are inclusions of opens. -/
theorem restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap {Z Y : Scheme.{u}}
    (i : Z ⟶ Y) [IsImmersion i] (V : Y.Opens) {W : Z.Opens} (hW : W = i ⁻¹ᵁ V)
    {S T : Scheme.{u}} (α : W.toScheme ≅ S) (g : S ⟶ T) (j : T ⟶ V.toScheme)
    [IsOpenImmersion j] (hfac : α.hom ≫ g ≫ j ≫ V.ι = W.ι ≫ i)
    (L : W.toScheme ⟶ V.toScheme) (hL : (α.hom ≫ g) ≫ j = L)
    (U : W.toScheme.Opens) (hU : U = W.ι ⁻¹ᵁ W)
    (P : T.Opens) (hP : P = j ⁻¹ᵁ (V.ι ⁻¹ᵁ V))
    (ν : W.ι ''ᵁ U ⟶ i ⁻¹ᵁ V) (ρ : U ⟶ (α.hom ≫ g) ⁻¹ᵁ P)
    (y : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op V))
    (y' : (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom).val.obj (op (V.ι ⁻¹ᵁ V)))
    (hy' : (CategoryTheory.Limits.kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom L.toLRSHom.toShHom))).val.app (op (V.ι ⁻¹ᵁ V)) y' =
      (V.ι.appIso (V.ι ⁻¹ᵁ V)).hom
        ((CategoryTheory.Limits.kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom i.toLRSHom.toShHom))).val.app (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ V)))
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.map
            (homOfLE (V.ι.image_preimage_le V)).op y)))
    (x : (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom).val.obj (op P))
    (hxy : (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom).val.map
        (eqToHom hP).op
        ((Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq
          (α.hom ≫ g) j L hL).val.app (op (V.ι ⁻¹ᵁ V)) y') = x) :
    (restrictConormalIsoOfOpenFactor i V hW α g j hfac).hom.val.app (op U)
        ((Stacks.Conormal.conormalSheaf i).val.map ν.op
          ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op V) y)) =
      ((modulePullback α.hom.toLRSHom.toShHom).obj
          ((modulePullback g.toLRSHom.toShHom).obj
            (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val.map ρ.op
        (((modulePullbackPushforwardAdjunction α.hom.toLRSHom.toShHom).unit.app
              ((modulePullback g.toLRSHom.toShHom).obj
                (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val.app
            (op (g ⁻¹ᵁ P))
          (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
                (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom)).val.app (op P)
            ((Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
              α g).hom.val.app (op P) x))) := by
  subst hW
  subst hU
  subst hP
  replace hxy : (Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq
      (α.hom ≫ g) j L hL).val.app (op (V.ι ⁻¹ᵁ V)) y' = x := by
    refine Eq.trans ?_ hxy
    exact (map_self_apply (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom).val
      _ _).symm
  obtain rfl : L = i ∣_ V :=
    (cancel_mono V.ι).mp ((congrArg (fun t => t ≫ V.ι) hL).symm.trans
      ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
        (hfac.trans (morphismRestrict_ι i V).symm))))
  obtain rfl : ν = homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ V)) := Subsingleton.elim _ _
  have hy'eq : y' = (Stacks.Conormal.Restriction.restrictIdealSheafIso' i V).hom.val.app
      (op (V.ι ⁻¹ᵁ V))
      ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.map
        (homOfLE (V.ι.image_preimage_le V)).op y) :=
    Stacks.Conormal.Locality.idealSheaf_section_injective (i ∣_ V) (V.ι ⁻¹ᵁ V)
      (hy'.trans (Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι i V (V.ι ⁻¹ᵁ V) _).symm)
  have hsplit : restrictConormalIsoOfOpenFactor i V rfl α g j hfac =
      (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapIso
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i) ≪≫
        Stacks.Conormal.Locality.conormalRestrictIso i V ≪≫
          (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) j (i ∣_ V) hL ≪≫
            Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource
              α g) :=
    rfl
  have he : (i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V) = (i ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ V) :=
    Stacks.Conormal.Locality.preimage_ι_preimage_eq i V
  have hF1 : ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapIso
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i)).hom.val.app
        (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V)))
        ((Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ V))).op
          ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op V) y)) =
      ((Scheme.Modules.pullback i).obj
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).val.map
        (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ V))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).val.app (op V) y) := by
    refine Eq.trans (Stacks.Conormal.Locality.restrictFunctor_map_val_app (i ⁻¹ᵁ V)
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).hom
      ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V)) _) ?_
    refine Eq.trans (PresheafOfModules.naturality_apply
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).hom.val
      (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ V))).op _) ?_
    exact congrArg (fun w => ((Scheme.Modules.pullback i).obj
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).val.map
        (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ V))).op w)
      (Stacks.Immersion.conormalSheafIsoPullbackSelf_hom_canonicalConormalQuotientMap i V y)
  refine Eq.trans (congrArg (fun e' => e'.hom.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V)))
      ((Stacks.Conormal.conormalSheaf i).val.map
        (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ V))).op
        ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op V) y))) hsplit) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapIso
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i)).hom
    (Stacks.Conormal.Locality.conormalRestrictIso i V ≪≫
      (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) j (i ∣_ V) hL ≪≫
        Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource
          α g)).hom (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V))) _) ?_
  refine Eq.trans (congrArg (fun w =>
    (Stacks.Conormal.Locality.conormalRestrictIso i V ≪≫
      (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) j (i ∣_ V) hL ≪≫
        Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource
          α g)).hom.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V))) w) hF1) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (Stacks.Conormal.Locality.conormalRestrictIso i V).hom
    (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) j (i ∣_ V) hL ≪≫
      Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource
        α g).hom (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V))) _) ?_
  refine Eq.trans (congrArg (fun w =>
    (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) j (i ∣_ V) hL ≪≫
      Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource
        α g).hom.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V))) w)
    (Stacks.Conormal.Locality.conormalRestrictIso_unit_app i V y)) ?_
  refine Eq.trans (congrArg (fun w =>
    (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) j (i ∣_ V) hL ≪≫
        Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource
          α g).hom.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback (i ∣_ V)).obj
          (Stacks.ClosedImmersion.idealSheaf (i ∣_ V).toLRSHom.toShHom)).val.map
        (eqToHom he).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ V)).unit.app
            (Stacks.ClosedImmersion.idealSheaf (i ∣_ V).toLRSHom.toShHom)).val.app
          (op (V.ι ⁻¹ᵁ V)) w))) hy'eq.symm) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) j (i ∣_ V) hL ≪≫
      Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource
        α g).hom.val (eqToHom he).op _) ?_
  refine Eq.trans (congrArg (fun w =>
    ((modulePullback α.hom.toLRSHom.toShHom).obj
        ((modulePullback g.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val.map (eqToHom he).op w)
    (Stacks.Conormal.OpenFactorizations.pullbackIdealSheafIsoOfCompEq_trans_isoOfIsoSource_hom_unit
      α g j (i ∣_ V) hL (V.ι ⁻¹ᵁ V) (eqToHom he.symm ≫ ρ) y' x hxy)) ?_
  refine Eq.trans (PresheafOfModules.map_comp_apply
    (M := ((modulePullback α.hom.toLRSHom.toShHom).obj
      ((modulePullback g.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val)
    (eqToHom he.symm ≫ ρ).op (eqToHom he).op _).symm ?_
  exact PresheafOfModules.congr_map_apply
    (M := ((modulePullback α.hom.toLRSHom.toShHom).obj
      ((modulePullback g.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val)
    (f := (eqToHom he.symm ≫ ρ).op ≫ (eqToHom he).op) (g := ρ.op) (Subsingleton.elim _ _) _

end Stacks.Conormal

namespace Stacks.ProjectiveBundleConormal

section ZeroSectionTarget

open SymmetricAlgebra

/-- **The target computation of [Stacks, Tag 0B3V] clause 3, over an open on which the immersion
is the zero section of an affine bundle, read on the conormal generator.** Let `i : Z ⟶ Y` be an
immersion, `V` an open of `Y` whose preimage is `W`, and suppose `i|_W` factors as an isomorphism
`α : W ≅ Spec A`, the zero section of the affine bundle `𝐀(K) = Spec (Sym_A K)`, and an open
immersion `j` of that bundle into `V`. Then the identification of `𝒞_i|_W` with `K^~` pulled back
along `α` — `Stacks.Conormal.restrictConormalIsoOfOpenFactor` followed by
`Stacks.ProjectiveBundleConormal.conormalZeroSectionIso` — carries the conormal generator named
by a section `y` of `ℐ_i` over `V` to the canonical global section of `K^~` named by the
derivative at the origin of the corresponding element `κ` of the augmentation ideal.

The hypotheses other than `hxκ` are those of
`Stacks.Conormal.restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap`, with both
opens taken to be `⊤`; `hxκ` identifies the section `x` of `ℐ_{α ≫ zeroSection}` with the
generator of `I^~` named by `κ`. -/
theorem restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsImmersion i] (V : Y.Opens) {W : Z.Opens}
    (hW : W = i ⁻¹ᵁ V) (A K : Type u) [CommRing A] [AddCommGroup K] [Module A K]
    (α : (↑W : Scheme.{u}) ≅ Spec (CommRingCat.of A))
    (j : Spec (symRing A K) ⟶ V.toScheme) [IsOpenImmersion j]
    (hfac : α.hom ≫ zeroSection A K ≫ j ≫ V.ι = W.ι ≫ i)
    (L : (↑W : Scheme.{u}) ⟶ V.toScheme) (hL : (α.hom ≫ zeroSection A K) ≫ j = L)
    (hP : (⊤ : (Spec (symRing A K)).Opens) = j ⁻¹ᵁ (V.ι ⁻¹ᵁ V))
    (ν : W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens) ⟶ i ⁻¹ᵁ V)
    (y : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op V))
    (y' : (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom).val.obj (op (V.ι ⁻¹ᵁ V)))
    (hy' : (CategoryTheory.Limits.kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom L.toLRSHom.toShHom))).val.app (op (V.ι ⁻¹ᵁ V)) y' =
      (V.ι.appIso (V.ι ⁻¹ᵁ V)).hom
        ((CategoryTheory.Limits.kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom i.toLRSHom.toShHom))).val.app (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ V)))
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.map
            (homOfLE (V.ι.image_preimage_le V)).op y)))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (α.hom ≫ zeroSection A K).toLRSHom.toShHom).val.obj (op ⊤))
    (hxy : (Stacks.ClosedImmersion.idealSheaf
          (α.hom ≫ zeroSection A K).toLRSHom.toShHom).val.map (eqToHom hP).op
        ((Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq
          (α.hom ≫ zeroSection A K) j L hL).val.app (op (V.ι ⁻¹ᵁ V)) y') = x)
    (κ : augIdealOf A K)
    (hxκ : (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
          α (zeroSection A K)).hom.val.app (op ⊤) x =
      (zeroSectionIdealSheafIso A K).hom.val.app (op ⊤)
        (tilde.toOpen (augIdealModule A K) ⊤ κ)) :
    (Stacks.Conormal.restrictConormalIsoOfOpenFactor i V hW α (zeroSection A K) j hfac ≪≫
          (Scheme.Modules.pullback α.hom).mapIso
            ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf (zeroSection A K)).symm ≪≫
              conormalZeroSectionIso A K)).hom.val.app
        (op (⊤ : (↑W : Scheme.{u}).Opens))
        ((Stacks.Conormal.conormalSheaf i).val.map ν.op
          ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op V) y)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction α.hom).unit.app
          (tilde (ModuleCat.of (CommRingCat.of A) K))).val.app (op ⊤)
        (tilde.toOpen (ModuleCat.of (CommRingCat.of A) K) ⊤
          (augDeriv (κ : SymmetricAlgebra A K))) := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (Stacks.Conormal.restrictConormalIsoOfOpenFactor i V hW α (zeroSection A K) j hfac).hom
    ((Scheme.Modules.pullback α.hom).mapIso
      ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf (zeroSection A K)).symm ≪≫
        conormalZeroSectionIso A K)).hom (op (⊤ : (↑W : Scheme.{u}).Opens)) _) ?_
  refine Eq.trans (congrArg (fun w => ((Scheme.Modules.pullback α.hom).mapIso
      ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf (zeroSection A K)).symm ≪≫
        conormalZeroSectionIso A K)).hom.val.app (op (⊤ : (↑W : Scheme.{u}).Opens)) w)
    (Stacks.Conormal.restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap
      i V hW α (zeroSection A K) j hfac L hL ⊤ (W.ι_preimage_self).symm ⊤ hP ν
      (homOfLE (le_refl _)) y y' hy' x hxy)) ?_
  refine Eq.trans (congrArg (fun w =>
      ((Scheme.Modules.pullback α.hom).mapIso
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf (zeroSection A K)).symm ≪≫
            conormalZeroSectionIso A K)).hom.val.app (op (⊤ : (↑W : Scheme.{u}).Opens))
        (((modulePullback α.hom.toLRSHom.toShHom).obj
              ((modulePullback (zeroSection A K).toLRSHom.toShHom).obj
                (Stacks.ClosedImmersion.idealSheaf
                  (zeroSection A K).toLRSHom.toShHom))).val.map
          (homOfLE (le_refl (⊤ : (↑W : Scheme.{u}).Opens))).op
          (((modulePullbackPushforwardAdjunction α.hom.toLRSHom.toShHom).unit.app
                ((modulePullback (zeroSection A K).toLRSHom.toShHom).obj
                  (Stacks.ClosedImmersion.idealSheaf
                    (zeroSection A K).toLRSHom.toShHom))).val.app (op ⊤)
            (((modulePullbackPushforwardAdjunction
                    (zeroSection A K).toLRSHom.toShHom).unit.app
                  (Stacks.ClosedImmersion.idealSheaf
                    (zeroSection A K).toLRSHom.toShHom)).val.app (op ⊤) w)))) hxκ) ?_
  refine Eq.trans (congrArg (fun w =>
      ((Scheme.Modules.pullback α.hom).mapIso
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf (zeroSection A K)).symm ≪≫
            conormalZeroSectionIso A K)).hom.val.app (op (⊤ : (↑W : Scheme.{u}).Opens)) w)
    (Stacks.Conormal.map_self_apply _ _ _)) ?_
  refine Eq.trans (Stacks.Conormal.Locality.unit_naturality_app α.hom
    ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf (zeroSection A K)).symm ≪≫
      conormalZeroSectionIso A K).hom ⊤
    (((modulePullbackPushforwardAdjunction (zeroSection A K).toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf (zeroSection A K).toLRSHom.toShHom)).val.app (op ⊤)
      ((zeroSectionIdealSheafIso A K).hom.val.app (op ⊤)
        (tilde.toOpen (augIdealModule A K) ⊤ κ)))) ?_
  refine congrArg (fun w =>
    ((Scheme.Modules.pullbackPushforwardAdjunction α.hom).unit.app
        (tilde (ModuleCat.of (CommRingCat.of A) K))).val.app (op ⊤) w) ?_
  refine Eq.trans (congrArg (fun ii :
        (Scheme.Modules.pullback (zeroSection A K)).obj
            (Stacks.ClosedImmersion.idealSheaf (zeroSection A K).toLRSHom.toShHom) ≅
          tilde (ModuleCat.of (CommRingCat.of A) K) =>
      ii.hom.val.app (op (⊤ : (Spec (CommRingCat.of A)).Opens))
        (((modulePullbackPushforwardAdjunction (zeroSection A K).toLRSHom.toShHom).unit.app
              (Stacks.ClosedImmersion.idealSheaf
                (zeroSection A K).toLRSHom.toShHom)).val.app (op ⊤)
          ((zeroSectionIdealSheafIso A K).hom.val.app (op ⊤)
            (tilde.toOpen (augIdealModule A K) ⊤ κ))))
    (conormalSheafIsoPullbackSelf_symm_trans_conormalZeroSectionIso A K)) ?_
  exact conormalZeroSectionTildeIso_hom_unit_toOpen A K κ

end ZeroSectionTarget

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  {W : X.Opens} (hW : IsAffineOpen W)

include hσ e hqe in
/-- **The factorization of `σ` over a chart through the zero section of the affine bundle**, with
the chart of `Proj` composed into the inclusion of `π⁻¹W`. -/
theorem isoSpec_comp_zeroSection_comp_splitChart_comp_ι
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1) :
    hW.isoSpec.hom ≫
        zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫
          (splitChartMap (chartLinearForm Q W eL) s hs ≫
              (bundleOverIso E (symPieces E) hW).hom) ≫
            ((bundle E).toBase ⁻¹ᵁ W).ι =
      W.ι ≫ σ :=
  calc hW.isoSpec.hom ≫
        zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫
          (splitChartMap (chartLinearForm Q W eL) s hs ≫
              (bundleOverIso E (symPieces E) hW).hom) ≫
            ((bundle E).toBase ⁻¹ᵁ W).ι
      = hW.isoSpec.hom ≫
          zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫
            splitChartMap (chartLinearForm Q W eL) s hs ≫
              chartMap E (symPieces E) hW :=
        congrArg
          (fun t => hW.isoSpec.hom ≫
            zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫ t)
          ((Category.assoc _ _ _).trans
            (congrArg (fun t => splitChartMap (chartLinearForm Q W eL) s hs ≫ t)
              (bundleOverIso_hom_comp_ι E (symPieces E) hW)))
    _ = (hW.isoSpec.hom ≫
          zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫
            splitChartMap (chartLinearForm Q W eL) s hs) ≫ chartMap E (symPieces E) hW :=
        (congrArg (fun t => hW.isoSpec.hom ≫ t) (Category.assoc _ _ _).symm).trans
          (Category.assoc _ _ _).symm
    _ = chartSection E hW hσ ≫ chartMap E (symPieces E) hW :=
        congrArg (fun t => t ≫ chartMap E (symPieces E) hW)
          (chartSection_eq_isoSpec_comp_zeroSection E Q hσ e hqe hW eL s hs).symm
    _ = W.ι ≫ σ := chartSection_comp_chartMap E hW hσ

variable [IsImmersion σ]

include hσ e hqe in
/-- **The target of the conormal map of [Stacks, Tag 0B3V] clause 3, restricted to a chart, is
`(ker p)^~`.** Over an affine open `W` carrying a frame for `𝓛` and a section of `ℰ` at which the
chart's linear form takes the value `1`, the conormal sheaf of the section `σ` is the pullback
along `W ≅ Spec Γ(X, W)` of the quasi-coherent sheaf attached to the kernel of that linear form. -/
def restrictConormalTargetIsoTilde (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1) :
    (Scheme.Modules.restrictFunctor W.ι).obj (Stacks.Conormal.conormalSheaf σ) ≅
      (Scheme.Modules.pullback hW.isoSpec.hom).obj (tilde (chartKerModule Q W eL)) :=
  haveI : IsOpenImmersion (splitChartMap (chartLinearForm Q W eL) s hs ≫
      (bundleOverIso E (symPieces E) hW).hom) :=
    IsOpenImmersion.comp _ _
  Stacks.Conormal.restrictConormalIsoOfOpenFactor σ ((bundle E).toBase ⁻¹ᵁ W)
      (preimage_toBase_preimage E hσ W).symm hW.isoSpec
      (zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))
      (splitChartMap (chartLinearForm Q W eL) s hs ≫ (bundleOverIso E (symPieces E) hW).hom)
      (isoSpec_comp_zeroSection_comp_splitChart_comp_ι E Q hσ e hqe hW eL s hs) ≪≫
    (Scheme.Modules.pullback hW.isoSpec.hom).mapIso
      ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
            (zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))).symm ≪≫
        conormalZeroSectionIso Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))

end Stacks.ProjectiveBundleConormal

end
