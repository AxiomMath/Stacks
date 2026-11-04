module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantModules.Morphisms
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The internal hom of locally constant sheaves of modules

Let `(C, J)` be a site and `Λ` a commutative ring. This file proves Stacks Tag 093T (3): if `F`
is a locally constant sheaf of `Λ`-modules whose local constant values are finitely presented and
`G` is a locally constant sheaf of `Λ`-modules, then the internal hom
`SheafHom_{Λ̲}(F, G)` is again a locally constant sheaf of `Λ`-modules.

The argument is the one of the source. The assertion is local on `C`, so `F` and `G` may be
trivialized simultaneously: each is constant on a covering of any given object, the intersection
of the two covering sieves is covering, and a trivialization survives refinement with its value
unchanged. Over a member of the resulting covering the two sheaves are the constant sheaves on
modules `M` and `N` with `M` finitely presented, and then Tag 093T (1) — which is
`Stacks.ConstantSheaf.constantSheafHomIsoOfHom` — identifies the internal hom with the constant
sheaf on `Hom_Λ(M, N)`.

Turning that local computation into a statement about the restriction of the internal hom needs
one structural ingredient, which is proved here first: the internal hom commutes with restriction
to a slice site.

## Main definitions

* `Stacks.ConstantSheaf.overPullbackModuleSheafHomIso`: the restriction to `C/X` of
  `SheafHom_{Λ̲}(F, G)` is the internal hom of the restrictions,
  `SheafHom_{Λ̲}(F, G)|_X ≅ SheafHom_{Λ̲}(F|_X, G|_X)`.
* `Stacks.ConstantSheaf.IsFinitePresentationLocallyConstantModuleSheaf`: local constancy with
  finitely presented constant values.

## Main results

* `Stacks.ConstantSheaf.overPullbackModuleSheafHomIso_hom_app_apply`: on sections the above
  isomorphism restricts a local morphism along the iterated-slice functor `(C/X)/R ⥤ C/R.left`.
  This pins the isomorphism down rather than merely asserting that one exists.
* `Stacks.ConstantSheaf.isLocallyConstant_moduleSheafHom`: **Stacks Tag 093T (3)**.

## Implementation notes

**The structural isomorphism.** The sections of `SheafHom_{Λ̲}(F, G)|_X` over an object
`R` of `C/X` are the morphisms `F|_{R.left} ⟶ G|_{R.left}` on `C/R.left`, while the sections of
`SheafHom_{Λ̲}(F|_X, G|_X)` over `R` are the morphisms `(F|_X)|_R ⟶ (G|_X)|_R` on the iterated
slice `(C/X)/R`. The comparison is restriction along `CategoryTheory.Over.iteratedSliceForward`,
which is `Λ`-linear and natural on the nose; that it is bijective is the full faithfulness of the
equivalence of sheaf categories which the iterated-slice equivalence of sites induces, together
with the observation that restriction along `Over.iteratedSliceBackward` is a left inverse of it
definitionally. This is the `ModuleCat`-valued analogue of
`Stacks.SheafOfModules.InternalHom.internalHomOverIso`, which proves the corresponding statement
(Tag 0E8H) for sheaves of modules over a ringed site; neither form specializes to the other,
since a sheaf of `Λ`-modules in the sense used here is not a sheaf of modules over the constant
sheaf of rings on `Λ`.

**The finiteness hypothesis on `F`.** Stacks states (3) for an `F` which is locally constant and
*of finite presentation*. The hypothesis carried here is
`IsFinitePresentationLocallyConstantModuleSheaf`, local constancy with finitely presented constant
values. For a locally constant sheaf the two agree, which is exactly Tag 093N part (2)
(`Stacks.SheafOfModules.Constant.constantModuleSheaf_isFinitePresentation_iff`): over an object
whose empty sieve is not covering, a constant sheaf of modules is of finite presentation precisely
when its value is a finitely presented module, and over an object whose empty sieve *is* covering
both conditions hold, the empty family being a covering family there. This is the same phrasing
the library already uses for Tag 093S (3), where
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf` stands for
`SheafOfModules.IsFiniteType`
for the same reason; carrying the source's phrasing instead would additionally require the
comparison between sheaves of modules over the constant sheaf of rings on `Λ` and
`ModuleCat.{_} Λ`-valued sheaves, which the library does not have. Finitely presented constant
values is also the form the proof consumes.

**Universes.** As in `ConstantSheafHom.lean`, the internal hom raises the module universe: the
sections over `X` are indexed by `(Over X)ᵒᵖ`, which lives in `Type (max u v)`. The statement is
therefore made for modules in `ModuleCat.{max u v x} Λ`, the universe at which the internal hom
of two such sheaves is again such a sheaf, so that local constancy of the internal hom is a
statement about the same category of sheaves. This is forced by the shape of the assertion, not
chosen.

**`Λ` is a commutative ring**, where Stacks says only "a ring". Since the source states the
conclusion as a sheaf of `Λ`-modules — rather than of modules over the opposite ring or of abelian
groups — the hypothesis is a benign strengthening, and it is the one the ambient file already
carries.

## References

* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
* [Stacks Project, Tag 093N](https://stacks.math.columbia.edu/tag/093N)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w x

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]

/-! ### The internal hom commutes with restriction to a slice site -/

section Slice

variable (X : C) (F G : Sheaf J (ModuleCat.{max u v x} Λ))

/-- A morphism `F|_{R.left} ⟶ G|_{R.left}` on `C/R.left`, read as a morphism
`(F|_X)|_R ⟶ (G|_X)|_R` on the iterated slice `(C/X)/R`, by restriction along
`CategoryTheory.Over.iteratedSliceForward`. -/
def moduleSheafHomSliceSection (R : Over X)
    (α : (J.overPullback (ModuleCat.{max u v x} Λ) R.left).obj F ⟶
      (J.overPullback (ModuleCat.{max u v x} Λ) R.left).obj G) :
    ((J.over X).overPullback (ModuleCat.{max u v x} Λ) R).obj
        ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj F) ⟶
      ((J.over X).overPullback (ModuleCat.{max u v x} Λ) R).obj
        ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj G) :=
  ⟨Functor.whiskerLeft (Over.iteratedSliceForward R).op α.hom⟩

/-- The equivalence of sheaf categories induced by the iterated-slice equivalence of sites
`(C/X)/R ≌ C/R.left`. -/
noncomputable def moduleSheafSliceCongr (R : Over X) :
    Sheaf ((J.over X).over R) (ModuleCat.{max u v x} Λ) ≌
      Sheaf (J.over R.left) (ModuleCat.{max u v x} Λ) :=
  (Over.iteratedSliceEquiv R).sheafCongr ((J.over X).over R) (J.over R.left) _

/-- Restriction along `CategoryTheory.Over.iteratedSliceBackward`, which is the functor of
`Stacks.ConstantSheaf.moduleSheafSliceCongr`, undoes restriction along
`CategoryTheory.Over.iteratedSliceForward`. -/
theorem moduleSheafSliceCongr_functor_map_sliceSection (R : Over X)
    (α : (J.overPullback (ModuleCat.{max u v x} Λ) R.left).obj F ⟶
      (J.overPullback (ModuleCat.{max u v x} Λ) R.left).obj G) :
    (moduleSheafSliceCongr J Λ X R).functor.map (moduleSheafHomSliceSection J Λ X F G R α) = α :=
  rfl

/-- Reading a section of the internal hom on the slice site, as a morphism of presheaves of
`Λ`-modules on `C/X`. -/
def moduleSheafHomOverPullbackNatTrans :
    ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj (moduleSheafHom J Λ F G)).obj ⟶
      (moduleSheafHom (J.over X) Λ ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj F)
        ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj G)).obj where
  app R := ModuleCat.ofHom
    { toFun := fun α => moduleSheafHomSliceSection J Λ X F G R.unop α
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- Each component of `Stacks.ConstantSheaf.moduleSheafHomOverPullbackNatTrans` is bijective: it
is a left inverse, definitionally, of the action on morphisms of the fully faithful equivalence
`Stacks.ConstantSheaf.moduleSheafSliceCongr`. -/
theorem bijective_moduleSheafHomOverPullbackNatTrans_app (R : (Over X)ᵒᵖ) :
    Function.Bijective
      ((moduleSheafHomOverPullbackNatTrans J Λ X F G).app R).hom := by
  have hid := moduleSheafSliceCongr_functor_map_sliceSection J Λ X F G R.unop
  exact ⟨Function.LeftInverse.injective hid, fun β =>
    ⟨(moduleSheafSliceCongr J Λ X R.unop).functor.map β,
      Functor.map_injective _ (hid _)⟩⟩

/-- Each component of `Stacks.ConstantSheaf.moduleSheafHomOverPullbackNatTrans` is an
isomorphism of `Λ`-modules. -/
instance isIso_moduleSheafHomOverPullbackNatTrans_app (R : (Over X)ᵒᵖ) :
    IsIso ((moduleSheafHomOverPullbackNatTrans J Λ X F G).app R) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_moduleSheafHomOverPullbackNatTrans_app J Λ X F G R

/-- The inverse of `Stacks.ConstantSheaf.moduleSheafHomOverPullbackNatTrans`, assembled from the
inverses of its components. -/
noncomputable def moduleSheafHomOverPullbackNatTransInv :
    (moduleSheafHom (J.over X) Λ ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj F)
        ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj G)).obj ⟶
      ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj (moduleSheafHom J Λ F G)).obj where
  app R := inv ((moduleSheafHomOverPullbackNatTrans J Λ X F G).app R)
  naturality _ _ f := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact ((moduleSheafHomOverPullbackNatTrans J Λ X F G).naturality f).symm

/-- **The internal hom commutes with restriction to a slice site.** The restriction to `C/X` of
`SheafHom_{Λ̲}(F, G)` is the internal hom of the restrictions of `F` and `G` to `C/X`. -/
@[sga "4 IV 12.3" "(b)"]
noncomputable def overPullbackModuleSheafHomIso :
    (J.overPullback (ModuleCat.{max u v x} Λ) X).obj (moduleSheafHom J Λ F G) ≅
      moduleSheafHom (J.over X) Λ ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj F)
        ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj G) :=
  { hom := ⟨moduleSheafHomOverPullbackNatTrans J Λ X F G⟩
    inv := ⟨moduleSheafHomOverPullbackNatTransInv J Λ X F G⟩
    hom_inv_id := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext R
      exact IsIso.hom_inv_id _
    inv_hom_id := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext R
      exact IsIso.inv_hom_id _ }

/-- On sections the isomorphism above restricts a local morphism along the iterated-slice
functor `(C/X)/R ⥤ C/R.left`. -/
theorem overPullbackModuleSheafHomIso_hom_app_apply (R : (Over X)ᵒᵖ)
    (α : ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj (moduleSheafHom J Λ F G)).obj.obj R) :
    ((overPullbackModuleSheafHomIso J Λ X F G).hom.hom.app R).hom α =
      moduleSheafHomSliceSection J Λ X F G R.unop α :=
  rfl

end Slice

/-! ### Local constancy with finitely presented values -/

section FinitePresentation

/-- **Locally constant of finite presentation.** A sheaf of `Λ`-modules `F` is locally constant of
finite presentation when every object `U` of the site has a covering family `V i ⟶ U` such that the
restriction of `F` to each `C/V i` is isomorphic to the constant sheaf attached to a finitely
presented `Λ`-module.

For a locally constant sheaf this is Stacks Tag 093N part (2)'s reformulation of finite
presentation of the sheaf; see the implementation notes. -/
@[sga "4 IX 2.0"]
def IsFinitePresentationLocallyConstantModuleSheaf (F : Sheaf J (ModuleCat.{max u v x} Λ)) :
    Prop :=
  ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U ∧ ∀ i,
      ∃ E : ModuleCat.{max u v x} Λ, Module.FinitePresentation Λ (E : Type (max u v x)) ∧
        Nonempty ((constantSheaf (J.over (V i)) (ModuleCat.{max u v x} Λ)).obj E ≅
          (J.overPullback (ModuleCat.{max u v x} Λ) (V i)).obj F)

/-- A sheaf of `Λ`-modules which is locally constant of finite presentation is locally
constant. -/
theorem isLocallyConstant_of_isFinitePresentationLocallyConstantModuleSheaf
    (F : Sheaf J (ModuleCat.{max u v x} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf J Λ F) : IsLocallyConstant J F where
  exists_cover U := by
    obtain ⟨I, V, f, hf, h⟩ := hF U
    exact ⟨I, V, f, hf, fun i => (h i).elim fun E ⟨_, e⟩ => ⟨E, e⟩⟩

end FinitePresentation

/-! ### Tag 093T (3) -/

section Main

/-- **Stacks Project, Tag 093T (3).** If `F` is a locally constant sheaf of `Λ`-modules of finite
presentation and `G` is a locally constant sheaf of `Λ`-modules, then the internal hom
`SheafHom_{Λ̲}(F, G)` is a locally constant sheaf of `Λ`-modules. -/
@[stacks 093T "sheafHom of locally constant sheaves"]
theorem isLocallyConstant_moduleSheafHom (F G : Sheaf J (ModuleCat.{max u v x} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf J Λ F) [IsLocallyConstant J G] :
    IsLocallyConstant J (moduleSheafHom J Λ F G) where
  exists_cover U := by
    obtain ⟨I, V, f, hf, hFV⟩ := hF U
    obtain ⟨I', W, g, hg, hGW⟩ := IsLocallyConstant.exists_cover (J := J) (F := G) U
    obtain ⟨K, Z, p, hp⟩ := (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g).exists_eq_ofArrows
    refine ⟨K, Z, p, hp ▸ J.intersection_covering hf hg, fun k => ?_⟩
    have hk : (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g) (p k) :=
      hp ▸ Sieve.ofArrows_mk Z p k
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff V f (p k)).mp hk.1
    obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff W g (p k)).mp hk.2
    obtain ⟨M, hM, ⟨eF⟩⟩ := hFV i
    obtain ⟨N, ⟨eG⟩⟩ := (hGW j).mem_essImage
    have := hM
    have : ∀ Y : Over (Z k),
        HasSheafify ((J.over (Z k)).over Y) (ModuleCat.{max u v x} Λ) := fun Y =>
      hasSheafify_over_moduleCat.{max u v, v, w, x} (J.over (Z k)) Λ Y
    exact ⟨⟨ModuleCat.of Λ (M ⟶ N),
      ⟨constantSheafHomIsoOfHom (J.over (Z k)) Λ M N ≪≫
        (moduleSheafHomMapIso (J.over (Z k)) Λ
          (overPullbackIsoOfMapModule J a F M eF)
          (overPullbackIsoOfMapModule J b G N eG)) ≪≫
        (overPullbackModuleSheafHomIso J Λ (Z k) F G).symm⟩⟩⟩

end Main

end Stacks.ConstantSheaf

end
