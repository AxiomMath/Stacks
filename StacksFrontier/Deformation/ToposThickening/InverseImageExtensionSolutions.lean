module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.Deformation.ToposThickening.BaseThickeningInverseImage
public import StacksFrontier.Deformation.ToposThickening.InverseImageExtensionComparison
public import StacksFrontier.Deformation.ToposThickening.ExtensionPresentationRemark
import StacksCore.Tactic.StacksAttribute

/-!
# The extensions `𝒪'₁` and `𝒪'₂` of Stacks 0GQ8 as square-zero extensions of `g⁻¹𝒪_𝒞`

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi, `ℱ` an `𝒪_𝒞`-module, `𝒢` an `𝒪_𝒟`-module, `c : g^*ℱ ⟶ 𝒢` an `𝒪_𝒟`-linear map,
`0 ⟶ ℱ ⟶ 𝒪_{𝒞'} ⟶ 𝒪_𝒞 ⟶ 0` an extension of `f⁻¹𝒪_ℬ`-algebras and
`0 ⟶ 𝒢 ⟶ 𝒪_{𝒟'} ⟶ 𝒪_𝒟 ⟶ 0` an extension of `g⁻¹f⁻¹𝒪_ℬ`-algebras, as in **Stacks 0GQ7**. The
two extensions are taken exactly as **Stacks 0GQ5** classifies them: solutions `QC` and `QD` of
the problems `ofTrivialBase f ℱ` and `ofTrivialBase (f ∘ g) 𝒢`.

**Stacks 0GQ8** builds two extensions of `g⁻¹𝒪_𝒞` by `𝒢` as `g⁻¹f⁻¹𝒪_ℬ`-algebras — the pushout
`𝒪'₁` of `g⁻¹𝒪_{𝒞'}` along `c : g⁻¹ℱ ⟶ 𝒢` and the pullback `𝒪'₂` of `𝒪_{𝒟'}` along
`g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟` — and shows by a diagram chase that a morphism
`g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` over `(Sh(ℬ), 𝒪_ℬ)` compatible with `g` and `c` exists
if and only if `𝒪'₁ ≅ 𝒪'₂`. This file states those three assertions for these inputs, with
`𝒪'₁` and `𝒪'₂` read as solutions of the one problem of Stacks 0GQ5 in which the remark
classifies them: the problem `inverseImageProblem f g 𝒢` of the ringed topos
`(Sh(𝒟), g⁻¹𝒪_𝒞)` over `(Sh(ℬ), 𝒪_ℬ)` and the `g⁻¹𝒪_𝒞`-module `𝒢`.

## Main definitions

* `Deformation.ToposThickening.InverseImageExtension.Data.ofSolutions`: the site-level input of
  `StacksFrontier/Deformation/ToposThickening/InverseImageExtensionComparison.lean` built from
  `QC`, `QD` and `c`, with every field derived.
* `Deformation.ToposThickening.InverseImageExtension.inverseImageProblem`: the problem of
  Stacks 0GQ5 for `(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `𝒢`.
* `Deformation.ToposThickening.InverseImageExtension.pushoutSolution` and `.pullbackSolution`:
  `𝒪'₁` and `𝒪'₂` as solutions of that problem.
* `Deformation.ToposThickening.InverseImageExtension.CompatibleMorphism`: a morphism of ringed
  topoi `g'` inducing `g`, over `(Sh(ℬ), 𝒪_ℬ)`, compatible with `g` and `c`.

## Main results

* `Deformation.ToposThickening.InverseImageExtension.existsUnique_invKernelIncl`: `g⁻¹ℱ` is the
  kernel of `g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞`, the left exactness of `g⁻¹`.
* `Deformation.ToposThickening.InverseImageExtension.comp_fSharpInverseImage_eq`: the structure
  map of a composite of morphisms of ringed topoi, in inverse-image form.
* `Deformation.ToposThickening.InverseImageExtension.structureHom_comp_inducingHom_eq_iff`: `g'`
  lies over `(Sh(ℬ), 𝒪_ℬ)` exactly when its comorphism is a map of `g⁻¹f⁻¹𝒪_ℬ`-algebras.
* `Deformation.ToposThickening.InverseImageExtension.nonempty_compatibleMorphism_iff_isomorphic`:
  **the criterion of Stacks 0GQ8**.

## Implementation notes

The constructions and the diagram chase are those of the ringed-space twin
`Stacks.Deformation.InverseImageExtension.Data` (**Stacks 0GQ2**) on the site of `𝒟`, through
`InverseImageExtension.Data`. Its two structural fields about `𝒢` (`inr_mul_inr`, `smul_inr`)
and the map out of the kernel of `g⁻¹`(reduction) are derived here from `QD` and `c`; the
module `𝒢` over `g⁻¹𝒪_{𝒞'}` is the restriction of the `𝒪_𝒟`-module `𝒢` along
`g^♯ ∘ g⁻¹`(reduction). The base rings `(f ∘ g)⁻¹𝒪_ℬ` and `g⁻¹f⁻¹𝒪_ℬ` are compared by
`baseIso`, the identity on sections.

## References

* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor pushforwardCommRingFunctor
  commRingImageAdjunction)
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafCompIso)

universe u v' u' w'

/-! ### An extension of algebras as a solution of the problem of a morphism and a module -/

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open Stacks.Sites.SqZeroExtension (AlgebraExtension)

variable {Z : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {h : RingedToposHom Z B}
  {M : SheafOfModules.{u} ((sheafCompose Z.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Z.O)}
  {S : Sheaf Z.J CommRingCat.{u}} {base : S ⟶ Z.O}

/-- **An extension of `S`-algebras `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` is a solution of the problem of
Stacks 0GQ5** attached to `h : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` and the `𝒪`-module `𝒢`, when `S` is
identified with `h⁻¹𝒪_ℬ` compatibly with the structure maps and `𝒪'` acts on its ideal `𝒢`
through `𝒪`. -/
def solutionOfAlgebraExtension (E : AlgebraExtension S Z.O base M.val.presheaf)
    (e : (inverseImageCommRingFunctor h.toToposHom).obj B.O ≅ S)
    (he : e.hom ≫ base = h.fSharpInverseImage)
    (hsmul : ∀ (U : Z.Cᵒᵖ) (a : E.O.obj.obj U) (n : M.val.obj U),
      a * E.inr U n = E.inr U ((show ((sheafCompose Z.J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj Z.O).val.obj U from E.proj.hom.app U a) • n)) :
    (ofTrivialBase h M).CompatibleFirstOrderThickening where
  extension := E.O
  reduction := E.proj
  locallySurjective := E.locallySurjective
  squareZero U := by
    refine le_antisymm ?_ bot_le
    rw [pow_two]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨n, rfl⟩ := (E.proj_app_eq_zero_iff U x).1 hx
    obtain ⟨m, rfl⟩ := (E.proj_app_eq_zero_iff U y).1 hy
    exact Ideal.mem_bot.2 (E.inr_mul_inr U n m)
  baseMap := e.hom ≫ E.fromBase
  baseMap_reduction := by
    change (e.hom ≫ E.fromBase) ≫ E.proj =
      (inverseImageCommRingFunctor h.toToposHom).map (𝟙 B.O) ≫ h.fSharpInverseImage
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, E.fromBase_comp_proj, he]
  kernelInclusion :=
    { val :=
      { app := fun U => ModuleCat.ofHom
          (X := ((SheafOfModules.restrictScalars
            ((sheafCompose Z.J (forget₂ CommRingCat.{u} RingCat.{u})).map E.proj)).obj M).val.obj U)
          (Y := (SheafOfModules.unit ((sheafCompose Z.J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj E.O)).val.obj U)
          { toFun := E.inr U
            map_add' := map_add (E.inr U)
            map_smul' := fun r n => (hsmul U r n).symm }
        naturality := fun {U V} f => by
          ext n
          exact (E.inr_map f n).symm } }
  kernelZero U n := E.proj_inr U n
  kernelUniversal U a ha := by
    obtain ⟨n, hn⟩ := (E.proj_app_eq_zero_iff U a).1 ha
    exact ⟨n, hn, fun m hm => E.inr_injective U (hm.trans hn.symm)⟩
  baseMap_ideal U a := by
    change (e.hom ≫ E.fromBase).hom.app U (0 : _) = E.inr U (0 : _)
    rw [map_zero, map_zero]

/-- **Two extensions of `S`-algebras are isomorphic as extensions exactly when they are
isomorphic as solutions of the problem of Stacks 0GQ5.** -/
theorem isomorphic_solutionOfAlgebraExtension_iff
    {E₁ E₂ : AlgebraExtension S Z.O base M.val.presheaf}
    (e : (inverseImageCommRingFunctor h.toToposHom).obj B.O ≅ S)
    (he : e.hom ≫ base = h.fSharpInverseImage)
    (hsmul₁ : ∀ (U : Z.Cᵒᵖ) (a : E₁.O.obj.obj U) (n : M.val.obj U),
      a * E₁.inr U n = E₁.inr U ((show ((sheafCompose Z.J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj Z.O).val.obj U from E₁.proj.hom.app U a) • n))
    (hsmul₂ : ∀ (U : Z.Cᵒᵖ) (a : E₂.O.obj.obj U) (n : M.val.obj U),
      a * E₂.inr U n = E₂.inr U ((show ((sheafCompose Z.J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj Z.O).val.obj U from E₂.proj.hom.app U a) • n)) :
    CompatibleFirstOrderThickening.Isomorphic (solutionOfAlgebraExtension E₁ e he hsmul₁)
        (solutionOfAlgebraExtension E₂ e he hsmul₂) ↔
      AlgebraExtension.Isomorphic E₁ E₂ := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨{ hom := φ.hom.hom
             base_comm := (cancel_epi e.hom).1 ((Category.assoc _ _ _).symm.trans φ.baseMap_comm)
             proj_comm := φ.reduction_comm
             inr_comm := φ.kernel_comm }⟩
  · rintro ⟨ψ⟩
    exact ⟨{ hom := @asIso _ _ _ _ ψ.hom ψ.isIso
             reduction_comm := ψ.proj_comm
             baseMap_comm := (Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) ψ.base_comm)
             kernel_comm := ψ.inr_comm }⟩

/-- The thickened ringed topos `(Sh(𝒞), 𝒪')` of a solution of the problem of Stacks 0GQ5. -/
abbrev CompatibleFirstOrderThickening.thickened {S : RingedToposExtensionProblem Z B}
    (P : S.CompatibleFirstOrderThickening) : RingedTopos.{u, u, u} :=
  { C := Z.C, J := Z.J, O := P.extension }

/-- **The structure morphism `(Sh(𝒞), 𝒪') ⟶ (Sh(ℬ), 𝒪_ℬ)` of a square-zero extension `𝒪'` of
`h⁻¹𝒪_ℬ`-algebras**: it induces `h` on the topoi, and its structure map is the adjunct of the
algebra structure `h⁻¹𝒪_ℬ ⟶ 𝒪'`. -/
def CompatibleFirstOrderThickening.structureHom
    (P : (ofTrivialBase h M).CompatibleFirstOrderThickening) :
    RingedToposHom P.thickened B where
  toToposHom := h.toToposHom
  fSharp := (commRingImageAdjunction h.toToposHom).homEquiv _ _ P.baseMap

/-- The inverse-image form of the structure morphism of a square-zero extension is its algebra
structure. -/
theorem CompatibleFirstOrderThickening.structureHom_fSharpInverseImage
    (P : (ofTrivialBase h M).CompatibleFirstOrderThickening) :
    P.structureHom.fSharpInverseImage = P.baseMap :=
  ((commRingImageAdjunction h.toToposHom).homEquiv _ _).symm_apply_apply P.baseMap

end Deformation.ToposThickening.RingedToposExtensionProblem

namespace Deformation.ToposThickening.InverseImageExtension

variable {Y X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-! ### The ringed topos `(Sh(𝒟), g⁻¹𝒪_𝒞)` -/

/-- The ringed topos `(Sh(𝒟), g⁻¹𝒪_𝒞)`, on which `𝒪'₁` and `𝒪'₂` are square-zero extensions. -/
abbrev inverseImageRingedTopos (g : RingedToposHom Y X) : RingedTopos.{u, u, u} :=
  { C := Y.C, J := Y.J, O := (invImage g).obj X.O }

/-- The morphism of ringed topoi `(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(𝒞), 𝒪_𝒞)` inducing `g` on the topoi,
whose structure map `g⁻¹𝒪_𝒞 ⟶ g⁻¹𝒪_𝒞` is the identity. -/
def toInverseImage (g : RingedToposHom Y X) : RingedToposHom (inverseImageRingedTopos g) X where
  toToposHom := g.toToposHom
  fSharp := (commRingImageAdjunction g.toToposHom).unit.app X.O

/-- The structure map of `(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(𝒞), 𝒪_𝒞)` is the identity of `g⁻¹𝒪_𝒞`. -/
theorem toInverseImage_fSharpInverseImage (g : RingedToposHom Y X) :
    (toInverseImage g).fSharpInverseImage = 𝟙 _ := by
  refine ((commRingImageAdjunction g.toToposHom).homEquiv _ _).symm_apply_eq.2 ?_
  exact ((commRingImageAdjunction g.toToposHom).homEquiv_id X.O).symm

/-- The comparison `g⁻¹f⁻¹𝒪_ℬ ≅ (f ∘ g)⁻¹𝒪_ℬ` of the iterated inverse image with the inverse image
along the composite. It is the identity on underlying sheaves of sets. -/
def baseIso (f : RingedToposHom X B) (g : RingedToposHom Y X) :
    (invImage g).obj (baseRing f) ≅
      (inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O :=
  pullbackCommRingSheafCompIso Y.J X.J g.toToposHom.inverseImage f.toToposHom.inverseImage B.O

/-- The inverse comparison `(f ∘ g)⁻¹𝒪_ℬ ⟶ g⁻¹f⁻¹𝒪_ℬ` is the identity on underlying sheaves of
sets. -/
theorem forget_map_baseIso_inv [Y.J.HasSheafCompose (forget CommRingCat.{u})]
    (f : RingedToposHom X B) (g : RingedToposHom Y X) :
    Y.forgetRing.map (baseIso f g).inv = 𝟙 _ := by
  have hh : Y.forgetRing.map (baseIso f g).hom = 𝟙 _ :=
    Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCompIso_hom_forget Y.J X.J
      g.toToposHom.inverseImage f.toToposHom.inverseImage B.O
  have h2 : Y.forgetRing.map (baseIso f g).hom ≫ Y.forgetRing.map (baseIso f g).inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [hh] at h2
  exact (Category.id_comp _).symm.trans h2

/-- **The structure map of a composite of morphisms of ringed topoi**, in inverse-image form: it
is the comparison `(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ`, followed by `g⁻¹` of the structure map of `f`,
followed by the structure map of `g`. -/
theorem comp_fSharpInverseImage_eq [Y.J.HasSheafCompose (forget CommRingCat.{u})]
    (f : RingedToposHom X B) (g : RingedToposHom Y X) :
    (f.comp g).fSharpInverseImage =
      (baseIso f g).inv ≫ (invImage g).map f.fSharpInverseImage ≫ g.fSharpInverseImage := by
  refine Y.forgetRing.map_injective ?_
  rw [AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget, Functor.map_comp,
    Functor.map_comp, forget_map_baseIso_inv]
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact congrArg (· ≫ Y.forgetRing.map g.fSharpInverseImage)
    (Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap Y.J
      g.toToposHom.inverseImage f.fSharpInverseImage).symm

/-! ### The ideal `g⁻¹ℱ` of `g⁻¹𝒪_{𝒞'}` -/

section InverseImageIdeal

open Stacks.Sheaves.ToposPullback (pullbackRingSheafMap pullbackModuleUnitIso
  isPullback_terminal_of_sections existsUnique_sections_of_isPullback
  sections_comp_eq_zero_of_isPullback)
open Stacks.Sheaves.RingedToposModules (inverseImageModules pullbackModuleObjRestrictScalarsIso)
open RingedToposExtensionProblem (ofTrivialBase)

variable {f : RingedToposHom X B}
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  (Q : (ofTrivialBase f F).CompatibleFirstOrderThickening)

/-- The inclusion `ℱ ⟶ 𝒪_{𝒞'}` of the square-zero ideal of a solution, on underlying sheaves of
sets. -/
noncomputable def kernelInclSheafSets :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)
        ((SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{u} RingCat.{u})).map Q.reduction)).obj F) ⟶
      Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension) :=
  (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)).map
    Q.kernelInclusion

/-- **The square-zero ideal `ℱ` of a solution is the kernel of its reduction**, as a pullback
square of sheaves of sets: the fibre of `𝒪_{𝒞'} ⟶ 𝒪_𝒞` over the zero section. -/
theorem isPullback_kernelInclSheafSets :
    IsPullback (kernelInclSheafSets Q) (terminal.from _)
      ((sheafCompose X.J (forget RingCat.{u})).map
        ((Stacks.forgetCommRingSheaf X.J).map Q.reduction))
      (Sheaf.ringZeroHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := by
  refine isPullback_terminal_of_sections _ _ _ ?_ (fun U b b' h ↦ ?_) fun U a ha ↦ ?_
  · refine Sheaf.hom_ext_sections fun U b ↦ ?_
    rw [(Sheaf.sectionsFunctor X.J U).map_comp_apply]
    exact Q.kernelZero U b
  · obtain ⟨n, -, hn⟩ := Q.kernelUniversal U (Q.kernelInclusion.val.app U b) (Q.kernelZero U b)
    exact (hn b rfl).trans (hn b' h.symm).symm
  · obtain ⟨n, hn, -⟩ := Q.kernelUniversal U a ha
    exact ⟨n, hn⟩

variable [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] (g : RingedToposHom Y X)

/-- `g⁻¹ℱ`, the inverse image of the square-zero ideal of a solution, as a `g⁻¹𝒪_𝒞`-module. -/
noncomputable abbrev invIdeal : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O)) :=
  (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The underlying morphism of sheaves of rings of `g⁻¹`(reduction), in the spelling the inverse
image of sheaves of rings produces it in. -/
theorem ringMap_invImage_map {A A' : Sheaf X.J CommRingCat.{u}} (π : A' ⟶ A) :
    (sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).map ((invImage g).map π) =
      pullbackRingSheafMap Y.J g.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf X.J).map π) :=
  Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap Y.J
    g.toToposHom.inverseImage π

/-- **The inclusion `g⁻¹ℱ ⟶ g⁻¹𝒪_{𝒞'}`**: the inverse image of the inclusion of the square-zero
ideal of a solution, read through the comparison of the inverse image of a restriction of
scalars with the restriction of scalars of the inverse image, and the identification of the
inverse image of a unit module with the unit module of the inverse image. -/
noncomputable def invKernelIncl :
    (SheafOfModules.restrictScalars ((sheafCompose Y.J
          (forget₂ CommRingCat.{u} RingCat.{u})).map ((invImage g).map Q.reduction))).obj
        (invIdeal g (F := F)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj Q.extension)) :=
  eqToHom (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj (invIdeal g (F := F)))
      (ringMap_invImage_map g Q.reduction)) ≫
    (pullbackModuleObjRestrictScalarsIso Y.J g.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf X.J).map Q.reduction) F).hom ≫
      (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)).map Q.kernelInclusion ≫
        (pullbackModuleUnitIso Y.J g.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)).inv

/-- The inclusion of `g⁻¹ℱ` is, on sections, the inverse image of the inclusion of `ℱ`. -/
theorem invKernelIncl_val_app (U : Y.Cᵒᵖ) (a : (invIdeal g (F := F)).val.obj U) :
    (invKernelIncl Q g).val.app U a =
      (Sheaf.sectionsFunctor Y.J U).map
        (g.toToposHom.inverseImage.map (kernelInclSheafSets Q)) a :=
  congrArg (fun y ↦ (((pullbackModuleObjRestrictScalarsIso Y.J g.toToposHom.inverseImage
      ((Stacks.forgetCommRingSheaf X.J).map Q.reduction) F).hom ≫
      (inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)).map Q.kernelInclusion ≫
        (pullbackModuleUnitIso Y.J g.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)).inv).val.app U) y)
    (restrictScalars_eqToHom_val_app (ringMap_invImage_map g Q.reduction)
      (invIdeal g (F := F)) U a)

/-- **The inclusion of `g⁻¹ℱ` is killed by `g⁻¹`(reduction).** -/
theorem invKernelIncl_mem (U : Y.Cᵒᵖ) (a : (invIdeal g (F := F)).val.obj U) :
    ((invImage g).map Q.reduction).hom.app U
        (show ((invImage g).obj Q.extension).obj.obj U from (invKernelIncl Q g).val.app U a) =
      0 := by
  rw [invKernelIncl_val_app]
  have h := sections_comp_eq_zero_of_isPullback Y.J g.toToposHom.inverseImage
    ((Stacks.forgetCommRingSheaf X.J).map Q.reduction) _ (isPullback_kernelInclSheafSets Q) U a
  rw [← ringMap_invImage_map g Q.reduction] at h
  exact h

/-- **A section of `g⁻¹𝒪_{𝒞'}` killed by `g⁻¹`(reduction) is the image of exactly one section of
`g⁻¹ℱ`**: the left exactness of `g⁻¹`. -/
theorem existsUnique_invKernelIncl (U : Y.Cᵒᵖ) (x : ((invImage g).obj Q.extension).obj.obj U)
    (hx : ((invImage g).map Q.reduction).hom.app U x = 0) :
    ∃! a : (invIdeal g (F := F)).val.obj U,
      (show ((invImage g).obj Q.extension).obj.obj U from (invKernelIncl Q g).val.app U a) =
        x := by
  have hx' : (Sheaf.sectionsFunctor Y.J U).map ((sheafCompose Y.J (forget RingCat.{u})).map
      (pullbackRingSheafMap Y.J g.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf X.J).map Q.reduction))) x = 0 := by
    rw [← ringMap_invImage_map g Q.reduction]
    exact hx
  obtain ⟨a, ha, huniq⟩ := existsUnique_sections_of_isPullback Y.J g.toToposHom.inverseImage
    ((Stacks.forgetCommRingSheaf X.J).map Q.reduction) _ (isPullback_kernelInclSheafSets Q) U x
    hx'
  exact ⟨a, (invKernelIncl_val_app Q g U a).trans ha,
    fun b hb ↦ huniq b ((invKernelIncl_val_app Q g U b).symm.trans hb)⟩

/-- The section of `g⁻¹ℱ` corresponding to a local section of `g⁻¹𝒪_{𝒞'}` killed by
`g⁻¹`(reduction). -/
noncomputable def invIdealPreimage (U : Y.Cᵒᵖ)
    (s : Stacks.Sites.Conormal.kernelIdeal ((invImage g).map Q.reduction).hom U) :
    (invIdeal g (F := F)).val.obj U :=
  (existsUnique_invKernelIncl Q g U s.1 s.2).exists.choose

/-- The image of `invIdealPreimage Q g U s` under `invKernelIncl Q g : g⁻¹ℱ ⟶ g⁻¹𝒪_{𝒞'}` is
`s`. -/
theorem invKernelIncl_invIdealPreimage (U : Y.Cᵒᵖ)
    (s : Stacks.Sites.Conormal.kernelIdeal ((invImage g).map Q.reduction).hom U) :
    (show ((invImage g).obj Q.extension).obj.obj U from
      (invKernelIncl Q g).val.app U (invIdealPreimage Q g U s)) = s.1 :=
  (existsUnique_invKernelIncl Q g U s.1 s.2).exists.choose_spec

/-- A local section of `g⁻¹ℱ` whose image in `g⁻¹𝒪_{𝒞'}` is `s` equals
`invIdealPreimage Q g U s`. -/
theorem invIdealPreimage_eq (U : Y.Cᵒᵖ)
    (s : Stacks.Sites.Conormal.kernelIdeal ((invImage g).map Q.reduction).hom U)
    (a : (invIdeal g (F := F)).val.obj U)
    (ha : (show ((invImage g).obj Q.extension).obj.obj U from
      (invKernelIncl Q g).val.app U a) = s.1) :
    invIdealPreimage Q g U s = a :=
  (existsUnique_invKernelIncl Q g U s.1 s.2).unique (invKernelIncl_invIdealPreimage Q g U s) ha

section Prescribed

variable [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}

/-- `𝒢` read as a `g⁻¹𝒪_𝒞`-module through `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`. -/
noncomputable abbrev restrictedIdeal (G : SheafOfModules.{u}
    ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)) :
    SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((invImage g).obj X.O)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).map g.fSharpInverseImage)).obj G

/-- **The adjoint `c : g⁻¹ℱ ⟶ 𝒢` of the prescribed `𝒪_𝒟`-linear map `c : g^*ℱ ⟶ 𝒢`**, under
the adjunction between extension and restriction of scalars along `g^♯` (Stacks 03CZ); it is
`g⁻¹𝒪_𝒞`-linear. -/
noncomputable def prescribedAdjoint
    (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G) :
    invIdeal g (F := F) ⟶ restrictedIdeal g G :=
  ((Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction Y.J
    (Stacks.Sheaves.RingedToposModules.fSharpCommRing g.toRingedToposModulesHom)
    (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property).homEquiv _ _) c

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The section of `g⁻¹ℱ` of a sum is the sum of the sections. -/
theorem invIdealPreimage_add (U : Y.Cᵒᵖ)
    (s t : Stacks.Sites.Conormal.kernelIdeal ((invImage g).map Q.reduction).hom U) :
    invIdealPreimage Q g U (s + t) = invIdealPreimage Q g U s + invIdealPreimage Q g U t := by
  refine invIdealPreimage_eq Q g U _ _ ?_
  refine (map_add ((invKernelIncl Q g).val.app U).hom _ _).trans ?_
  exact congrArg₂ (· + ·) (invKernelIncl_invIdealPreimage Q g U s)
    (invKernelIncl_invIdealPreimage Q g U t)

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The section of `g⁻¹ℱ` of `0` is `0`. -/
theorem invIdealPreimage_zero (U : Y.Cᵒᵖ) :
    invIdealPreimage Q g U 0 = 0 :=
  invIdealPreimage_eq Q g U _ _ (map_zero ((invKernelIncl Q g).val.app U).hom)

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The section of `g⁻¹ℱ` of `r • s` is `g⁻¹`(reduction)`(r) • ` that of `s`. -/
theorem invIdealPreimage_smul (U : Y.Cᵒᵖ) (r : ((invImage g).obj Q.extension).obj.obj U)
    (s : Stacks.Sites.Conormal.kernelIdeal ((invImage g).map Q.reduction).hom U) :
    invIdealPreimage Q g U (r • s) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O)).obj.obj U from
        ((invImage g).map Q.reduction).hom.app U r) •
        invIdealPreimage Q g U s := by
  refine invIdealPreimage_eq Q g U _ _ ?_
  refine (((invKernelIncl Q g).val.app U).hom.map_smul r (invIdealPreimage Q g U s)).trans ?_
  exact congrArg (r * ·) (invKernelIncl_invIdealPreimage Q g U s)

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The section of `g⁻¹ℱ` commutes with the restriction maps. -/
theorem invIdealPreimage_map {U V : Y.Cᵒᵖ} (i : U ⟶ V)
    (s : Stacks.Sites.Conormal.kernelIdeal ((invImage g).map Q.reduction).hom U) :
    invIdealPreimage Q g V ⟨(((invImage g).obj Q.extension).obj.map i).hom s.1,
        Stacks.Sites.Conormal.map_kernel _ i s.2⟩ =
      (invIdeal g (F := F)).val.map i (invIdealPreimage Q g U s) := by
  refine invIdealPreimage_eq Q g V _ _ ?_
  refine (PresheafOfModules.naturality_apply (invKernelIncl Q g).val i _).trans ?_
  exact congrArg (((invImage g).obj Q.extension).obj.map i).hom
    (invKernelIncl_invIdealPreimage Q g U s)

/-- **The prescribed map `c : g⁻¹ℱ ⟶ 𝒢` on the kernel ideal of `g⁻¹`(reduction)**: a local
section of `g⁻¹𝒪_{𝒞'}` killed by `g⁻¹`(reduction) is a section of `g⁻¹ℱ`, to which `c` is
applied. -/
noncomputable def prescribedRestriction
    (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G) :
    Stacks.Sites.Conormal.IdealRestriction ((invImage g).map Q.reduction)
      (restrictedIdeal g G) where
  app U :=
    { toFun := fun s => (prescribedAdjoint g c).val.app U (invIdealPreimage Q g U s)
      map_zero' := by
        rw [invIdealPreimage_zero]
        exact map_zero ((prescribedAdjoint g c).val.app U).hom
      map_add' := fun s t => by
        rw [invIdealPreimage_add]
        exact map_add ((prescribedAdjoint g c).val.app U).hom _ _ }
  app_smul U r s := by
    change (prescribedAdjoint g c).val.app U (invIdealPreimage Q g U (r • s)) = _
    rw [invIdealPreimage_smul]
    exact ((prescribedAdjoint g c).val.app U).hom.map_smul _ _
  app_map {U V} i s := by
    change (prescribedAdjoint g c).val.app V (invIdealPreimage Q g V _) = _
    rw [invIdealPreimage_map]
    exact PresheafOfModules.naturality_apply (prescribedAdjoint g c).val i _

/-- **The square-zero ideal `𝒢` of a solution, as the kernel of its reduction**, in the form the
fibre product of Stacks 0GQ2 consumes. -/
def kernelFibreInrData {Z : RingedTopos.{u, u, u}} [Z.J.HasSheafCompose (forget RingCat.{u})]
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {S : RingedToposExtensionProblem Z B} (P : S.CompatibleFirstOrderThickening) :
    Stacks.Sites.SqZeroPullback.FibreInrData P.reduction S.G.val.presheaf where
  app U := (P.kernelInclusion.val.app U).hom.toAddMonoidHom
  app_map f n := PresheafOfModules.naturality_apply P.kernelInclusion.val f n
  app_injective U a b h := by
    obtain ⟨n, -, hn⟩ := P.kernelUniversal U (P.kernelInclusion.val.app U a) (P.kernelZero U a)
    exact (hn a rfl).trans (hn b h.symm).symm
  range U a := ⟨fun h => let ⟨n, hn, _⟩ := P.kernelUniversal U a h; ⟨n, hn⟩,
    fun ⟨n, hn⟩ => hn ▸ P.kernelZero U n⟩

variable [Y.J.HasSheafCompose (forget CommRingCat.{u})]

/-- **The ringed-topos input of Stacks 0GQ8 built from the data of Stacks 0GQ7**: the extension
`0 ⟶ ℱ ⟶ 𝒪_{𝒞'} ⟶ 𝒪_𝒞 ⟶ 0` of `f⁻¹𝒪_ℬ`-algebras, the extension
`0 ⟶ 𝒢 ⟶ 𝒪_{𝒟'} ⟶ 𝒪_𝒟 ⟶ 0` of `(f ∘ g)⁻¹𝒪_ℬ = g⁻¹f⁻¹𝒪_ℬ`-algebras, both solutions of the
problem of Stacks 0GQ5, and the `𝒪_𝒟`-linear map `c : g^*ℱ ⟶ 𝒢`. Every field of
`InverseImageExtension.Data` is derived: the module `𝒢` over `g⁻¹𝒪_{𝒞'}` is its restriction
along `g^♯ ∘ g⁻¹`(reduction), the map out of the kernel of `g⁻¹`(reduction) is the adjoint of
`c` read through the left exactness of `g⁻¹`, and the two structural facts about `𝒢` are the
square-zero and linearity properties of the second solution. -/
noncomputable def Data.ofSolutions (QC : (ofTrivialBase f F).CompatibleFirstOrderThickening)
    (QD : (ofTrivialBase (f.comp g) G).CompatibleFirstOrderThickening)
    (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G) : Data f g where
  OC' := QC.extension
  reduction := QC.reduction
  locallySurjective_reduction := QC.locallySurjective
  fromBase := QC.baseMap
  G := (SheafOfModules.restrictScalars ((sheafCompose Y.J (forget₂ CommRingCat.{u}
    RingCat.{u})).map ((invImage g).map QC.reduction))).obj (restrictedIdeal g G)
  c := (prescribedRestriction QC g c).toPushoutData
  OD' := QD.extension
  p := QD.reduction
  locallySurjective_p := QD.locallySurjective
  ι := kernelFibreInrData QD
  inr_mul_inr U n m := by
    have hmem : (show QD.extension.obj.obj U from QD.kernelInclusion.val.app U n) *
        (show QD.extension.obj.obj U from QD.kernelInclusion.val.app U m) ∈
        RingHom.ker (QD.reduction.hom.app U).hom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (RingHom.mem_ker.2 (QD.kernelZero U n))
        (RingHom.mem_ker.2 (QD.kernelZero U m))
    rw [QD.squareZero U] at hmem
    exact hmem
  smul_inr U b a n hb := by
    have h1 := (QD.kernelInclusion.val.app U).hom.map_smul b (show G.val.obj U from n)
    exact h1.symm.trans (congrArg (fun r => (QD.kernelInclusion.val.app U).hom
      ((show ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O).val.obj U
        from r) • (show G.val.obj U from n))) hb)
  fromBaseBack := (baseIso f g).hom ≫ QD.baseMap
  base_comm := by
    have hD : (baseIso f g).hom ≫ QD.baseMap ≫ QD.reduction =
        (baseIso f g).hom ≫ (f.comp g).fSharpInverseImage :=
      congrArg (fun x : (inverseImageCommRingFunctor (f.comp g).toToposHom).obj B.O ⟶ Y.O =>
        (baseIso f g).hom ≫ x)
        (RingedToposExtensionProblem.baseMap_comp_reduction_ofTrivialBase QD)
    have hC : (invImage g).map (QC.baseMap ≫ QC.reduction) =
        (invImage g).map f.fSharpInverseImage :=
      congrArg (invImage g).map
        (RingedToposExtensionProblem.baseMap_comp_reduction_ofTrivialBase QC)
    refine (Category.assoc _ _ _).trans (hD.trans ?_)
    rw [comp_fSharpInverseImage_eq, Iso.hom_inv_id_assoc]
    exact (congrArg (· ≫ g.fSharpInverseImage) hC).symm

/-- **The problem of Stacks 0GQ5 in which `𝒪'₁` and `𝒪'₂` live**: square-zero extensions of
`g⁻¹𝒪_𝒞` by `𝒢` (read over `g⁻¹𝒪_𝒞` through `g^♯`) as algebras over
`(f ∘ g)⁻¹𝒪_ℬ = g⁻¹f⁻¹𝒪_ℬ`, i.e. the problem of the morphism
`(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and the module `𝒢`. -/
noncomputable abbrev inverseImageProblem (f : RingedToposHom X B) (g : RingedToposHom Y X)
    (G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)) :
    RingedToposExtensionProblem (inverseImageRingedTopos g) B :=
  ofTrivialBase (f.comp (toInverseImage g)) (restrictedIdeal g G)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The base ring of the problem of `𝒪'₁` and `𝒪'₂` is `(f ∘ g)⁻¹𝒪_ℬ`, and the comparison with
`g⁻¹f⁻¹𝒪_ℬ` carries its structure map to `g⁻¹f^♯`. -/
theorem baseIso_inv_comp_invImage_map (f : RingedToposHom X B) (g : RingedToposHom Y X) :
    (baseIso f g).inv ≫ (invImage g).map f.fSharpInverseImage =
      (f.comp (toInverseImage g)).fSharpInverseImage := by
  rw [comp_fSharpInverseImage_eq, toInverseImage_fSharpInverseImage]
  show _ = (baseIso f g).inv ≫ (invImage g).map f.fSharpInverseImage ≫ 𝟙 ((invImage g).obj X.O)
  rw [Category.comp_id]

variable [HasWeakSheafify Y.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective CommRingCat.{u}]
  (QC : (ofTrivialBase f F).CompatibleFirstOrderThickening)
  (QD : (ofTrivialBase (f.comp g) G).CompatibleFirstOrderThickening)
  (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G)

omit [HasWeakSheafify Y.J CommRingCat] [Y.J.WEqualsLocallyBijective CommRingCat] in
/-- The structure map `invBase` of `Data.ofSolutions g QC QD c`, precomposed with the inverse of
`baseIso f g : g⁻¹f⁻¹𝒪_ℬ ≅ (f ∘ g)⁻¹𝒪_ℬ`, is the structure map of `f.comp (toInverseImage g)`. -/
theorem ofSolutions_invBase :
    (baseIso f g).symm.hom ≫ (Data.ofSolutions g QC QD c).invBase =
      (f.comp (toInverseImage g)).fSharpInverseImage := by
  refine Eq.trans ?_ (baseIso_inv_comp_invImage_map f g)
  have h : (invImage g).map QC.baseMap ≫ (invImage g).map QC.reduction =
      (invImage g).map f.fSharpInverseImage :=
    ((invImage g).map_comp QC.baseMap QC.reduction).symm.trans
      (congrArg (invImage g).map
        (RingedToposExtensionProblem.baseMap_comp_reduction_ofTrivialBase QC))
  exact congrArg ((baseIso f g).inv ≫ ·) h

/-- **Stacks 0GQ8, the pushout `𝒪'₁`, as a square-zero extension of `g⁻¹𝒪_𝒞` by `𝒢`**: a
solution of `inverseImageProblem f g 𝒢`. -/
@[stacks 0GQ8 "the first construction: the pushout O'_1 of g⁻¹O_{C'} along c : g⁻¹F ⟶ G, an \
extension of g⁻¹O_C by G as g⁻¹f⁻¹O_B-algebras"]
noncomputable def pushoutSolution : (inverseImageProblem f g G).CompatibleFirstOrderThickening :=
  RingedToposExtensionProblem.solutionOfAlgebraExtension
    (Data.ofSolutions g QC QD c).pushoutExtension (baseIso f g).symm (ofSolutions_invBase g QC QD c)
    fun U a n => Stacks.Sites.SqZeroPushout.mul_pushoutInr _ _ U a n

/-- **Stacks 0GQ8, the pullback `𝒪'₂ = 𝒪_{𝒟'} ×_{𝒪_𝒟} g⁻¹𝒪_𝒞`, as a square-zero extension of
`g⁻¹𝒪_𝒞` by `𝒢`**: a solution of `inverseImageProblem f g 𝒢`. -/
@[stacks 0GQ8 "the second construction: the pullback O'_2 of O_{D'} along g^♯ : g⁻¹O_C ⟶ O_D, \
an extension of g⁻¹O_C by G as g⁻¹f⁻¹O_B-algebras", ega "0 18.2.5" "more general"]
noncomputable def pullbackSolution : (inverseImageProblem f g G).CompatibleFirstOrderThickening :=
  RingedToposExtensionProblem.solutionOfAlgebraExtension
    (Data.ofSolutions g QC QD c).pullbackExtension (baseIso f g).symm
    (ofSolutions_invBase g QC QD c)
    fun U z n => Stacks.Sites.SqZeroPullback.fibreMk_mul_fibreInr QD.reduction
      g.fSharpInverseImage (kernelFibreInrData QD) U z n _
      (((QD.kernelInclusion.val.app U).hom.map_smul
        (Stacks.Sites.SqZeroPullback.fibreVal QD.reduction g.fSharpInverseImage U z).1
          (show G.val.obj U from n)).symm.trans
        (congrArg (fun r => (QD.kernelInclusion.val.app U).hom
          ((show ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O).val.obj U
            from r) • (show G.val.obj U from n)))
          (Stacks.Sites.SqZeroPullback.fibreVal_mem QD.reduction g.fSharpInverseImage U z)))


/-- **The morphism of ringed topoi `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` inducing `g` on
the topoi with structure map `ψ : 𝒪_{𝒞'} ⟶ g_*𝒪_{𝒟'}`.** Every morphism of ringed topoi between
the two thickenings inducing `g` is of this form. -/
def inducingHom (ψ : QC.extension ⟶ (pushforwardCommRingFunctor g.toToposHom).obj QD.extension) :
    RingedToposHom QD.thickened QC.thickened where
  toToposHom := g.toToposHom
  fSharp := ψ

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J CommRingCat] [Y.J.WEqualsLocallyBijective CommRingCat] in
/-- **A morphism `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` inducing `g` lies over
`(Sh(ℬ), 𝒪_ℬ)`** — its composite with the structure morphism of `𝒪_{𝒞'}` is the structure
morphism of `𝒪_{𝒟'}` — exactly when its comorphism carries the algebra structure of
`g⁻¹𝒪_{𝒞'}` to that of `𝒪_{𝒟'}`. -/
theorem structureHom_comp_inducingHom_eq_iff
    (ψ : QC.extension ⟶ (pushforwardCommRingFunctor g.toToposHom).obj QD.extension) :
    QC.structureHom.comp (inducingHom g QC QD ψ) = QD.structureHom ↔
      (invImage g).map QC.baseMap ≫ (inducingHom g QC QD ψ).fSharpInverseImage =
        (baseIso f g).hom ≫ QD.baseMap := by
  have hinv : (QC.structureHom.comp (inducingHom g QC QD ψ)).fSharpInverseImage =
      (baseIso f g).inv ≫ (invImage g).map QC.baseMap ≫
        (inducingHom g QC QD ψ).fSharpInverseImage :=
    (comp_fSharpInverseImage_eq QC.structureHom (inducingHom g QC QD ψ)).trans
      (congrArg (fun a => (baseIso f g).inv ≫ (invImage g).map a ≫
          (inducingHom g QC QD ψ).fSharpInverseImage)
        (RingedToposExtensionProblem.CompatibleFirstOrderThickening.structureHom_fSharpInverseImage
          QC))
  have hD :=
    RingedToposExtensionProblem.CompatibleFirstOrderThickening.structureHom_fSharpInverseImage QD
  constructor
  · intro h
    have h' : RingedToposHom.mk (X := QD.thickened) (Y := B) (f.comp g).toToposHom
        (QC.structureHom.comp (inducingHom g QC QD ψ)).fSharp =
        RingedToposHom.mk (X := QD.thickened) (Y := B) (f.comp g).toToposHom
          QD.structureHom.fSharp := h
    have h2 : (QC.structureHom.comp (inducingHom g QC QD ψ)).fSharpInverseImage =
        QD.structureHom.fSharpInverseImage :=
      congrArg ((commRingImageAdjunction (f.comp g).toToposHom).homEquiv _ _).symm
        (eq_of_heq (RingedToposHom.mk.inj h').2)
    exact (Iso.inv_comp_eq _).1 (hinv.symm.trans (h2.trans hD))
  · intro h
    have h2 : (QC.structureHom.comp (inducingHom g QC QD ψ)).fSharpInverseImage =
        QD.structureHom.fSharpInverseImage :=
      hinv.trans (((Iso.inv_comp_eq _).2 h).trans hD.symm)
    show RingedToposHom.mk _ _ = RingedToposHom.mk _ _
    congr 1
    exact ((commRingImageAdjunction (f.comp g).toToposHom).homEquiv _ _).symm.injective h2

/-- **A morphism of ringed topoi `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` over
`(Sh(ℬ), 𝒪_ℬ)` compatible with `g` and `c`** (Stacks 0GQ7, 0GQ8): it induces `g` on the topoi
(it is `inducingHom ψ` for its structure map `ψ : 𝒪_{𝒞'} ⟶ g_*𝒪_{𝒟'}`), its composite with the
structure morphism `(Sh(𝒞), 𝒪_{𝒞'}) ⟶ (Sh(ℬ), 𝒪_ℬ)` is the structure morphism of
`(Sh(𝒟), 𝒪_{𝒟'})`, it reduces to `g` (its comorphism followed by `𝒪_{𝒟'} ⟶ 𝒪_𝒟` is
`g⁻¹`(reduction) followed by `g^♯`), and its comorphism `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` carries
`g⁻¹ℱ ⊂ g⁻¹𝒪_{𝒞'}` into `𝒢 ⊂ 𝒪_{𝒟'}` by the adjoint `g⁻¹ℱ ⟶ 𝒢` of `c : g^*ℱ ⟶ 𝒢`. -/
structure CompatibleMorphism where
  /-- The structure map `𝒪_{𝒞'} ⟶ g_*𝒪_{𝒟'}` of `g'`. -/
  fSharp : QC.extension ⟶ (pushforwardCommRingFunctor g.toToposHom).obj QD.extension
  /-- `g'` lies over `(Sh(ℬ), 𝒪_ℬ)`. -/
  over_base : QC.structureHom.comp (inducingHom g QC QD fSharp) = QD.structureHom
  /-- `g'` is compatible with `g`. -/
  over_g : (inducingHom g QC QD fSharp).fSharpInverseImage ≫ QD.reduction =
    (invImage g).map QC.reduction ≫ g.fSharpInverseImage
  /-- `g'` is compatible with `c`. -/
  compatible_c : ∀ (U : Y.Cᵒᵖ) (a : (invIdeal g (F := F)).val.obj U),
    (inducingHom g QC QD fSharp).fSharpInverseImage.hom.app U
        (show ((invImage g).obj QC.extension).obj.obj U from
          (invKernelIncl QC g).val.app U a) =
      QD.kernelInclusion.val.app U ((prescribedAdjoint g c).val.app U a)

/-- A compatible morphism of ringed topoi gives a compatible comorphism. -/
def CompatibleMorphism.toCompatibleHom (m : CompatibleMorphism g QC QD c) :
    (Data.ofSolutions g QC QD c).CompatibleHom where
  hom := (inducingHom g QC QD m.fSharp).fSharpInverseImage
  base_comm := (structureHom_comp_inducingHom_eq_iff g QC QD m.fSharp).1 m.over_base
  proj_comm := m.over_g
  kernel_comm U s :=
    (congrArg ((inducingHom g QC QD m.fSharp).fSharpInverseImage.hom.app U)
      (invKernelIncl_invIdealPreimage QC g U s)).symm.trans
      (m.compatible_c U (invIdealPreimage QC g U s))

/-- A compatible comorphism gives a compatible morphism of ringed topoi. -/
def CompatibleMorphism.ofCompatibleHom (h : (Data.ofSolutions g QC QD c).CompatibleHom) :
    CompatibleMorphism g QC QD c where
  fSharp := (commRingImageAdjunction g.toToposHom).homEquiv _ _ h.hom
  over_base := by
    refine (structureHom_comp_inducingHom_eq_iff g QC QD _).2 ?_
    have e : (inducingHom g QC QD ((commRingImageAdjunction g.toToposHom).homEquiv _ _
        h.hom)).fSharpInverseImage = h.hom :=
      ((commRingImageAdjunction g.toToposHom).homEquiv _ _).symm_apply_apply h.hom
    rw [e]
    exact h.base_comm
  over_g := by
    have e : (inducingHom g QC QD ((commRingImageAdjunction g.toToposHom).homEquiv _ _
        h.hom)).fSharpInverseImage = h.hom :=
      ((commRingImageAdjunction g.toToposHom).homEquiv _ _).symm_apply_apply h.hom
    rw [e]
    exact h.proj_comm
  compatible_c U a := by
    have e : (inducingHom g QC QD ((commRingImageAdjunction g.toToposHom).homEquiv _ _
        h.hom)).fSharpInverseImage = h.hom :=
      ((commRingImageAdjunction g.toToposHom).homEquiv _ _).symm_apply_apply h.hom
    rw [e]
    have hs := h.kernel_comm U ⟨_, invKernelIncl_mem QC g U a⟩
    refine hs.trans ?_
    exact congrArg (fun x => QD.kernelInclusion.val.app U ((prescribedAdjoint g c).val.app U x))
      (invIdealPreimage_eq QC g U _ a rfl)

/-- **The criterion of Stacks 0GQ8, read on comorphisms**: a compatible comorphism
`g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` exists if and only if `𝒪'₁` and `𝒪'₂` are isomorphic as solutions of the
problem of Stacks 0GQ5 for `(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `𝒢`. -/
theorem nonempty_compatibleHom_iff_isomorphic_solutions :
    Nonempty (Data.ofSolutions g QC QD c).CompatibleHom ↔
      RingedToposExtensionProblem.CompatibleFirstOrderThickening.Isomorphic
        (pushoutSolution g QC QD c) (pullbackSolution g QC QD c) :=
  (Data.ofSolutions g QC QD c).nonempty_compatibleHom_iff_isomorphic.trans
    (RingedToposExtensionProblem.isomorphic_solutionOfAlgebraExtension_iff
      (Z := inverseImageRingedTopos g) (h := f.comp (toInverseImage g)) (M := restrictedIdeal g G)
      (E₁ := (Data.ofSolutions g QC QD c).pushoutExtension)
      (E₂ := (Data.ofSolutions g QC QD c).pullbackExtension)
      (baseIso f g).symm (ofSolutions_invBase g QC QD c) _ _).symm

/-- **Stacks Project, Tag 0GQ8, the diagram chase.** A morphism
`g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` of ringed topoi over `(Sh(ℬ), 𝒪_ℬ)` compatible with `g`
and `c` exists if and only if the pushout `𝒪'₁` and the pullback `𝒪'₂` are isomorphic as
`g⁻¹f⁻¹𝒪_ℬ`-algebra extensions of `g⁻¹𝒪_𝒞` by `𝒢`. -/
@[stacks 0GQ8 "the diagram chase: a morphism g' over (Sh(B), O_B) compatible with g and c \
exists iff O'_1 and O'_2 are isomorphic as g⁻¹f⁻¹O_B-algebra extensions of g⁻¹O_C by G"]
theorem nonempty_compatibleMorphism_iff_isomorphic :
    Nonempty (CompatibleMorphism g QC QD c) ↔
      RingedToposExtensionProblem.CompatibleFirstOrderThickening.Isomorphic
        (pushoutSolution g QC QD c) (pullbackSolution g QC QD c) :=
  Iff.trans
    ⟨fun ⟨m⟩ => ⟨m.toCompatibleHom⟩,
      fun ⟨h⟩ => ⟨CompatibleMorphism.ofCompatibleHom g QC QD c h⟩⟩
    (nonempty_compatibleHom_iff_isomorphic_solutions g QC QD c)

end Prescribed

end InverseImageIdeal

end Deformation.ToposThickening.InverseImageExtension


end
