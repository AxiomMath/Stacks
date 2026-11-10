module

public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ClosedImmersion

/-!
# The product of the square-zero ideal with a module over a thickening

Let `i : (Sh(C), O') ⟶ (Sh(D), O)` be a first order thickening of ringed topoi with square-zero
ideal `I`, and let `G'` be a sheaf of `O`-modules. The *ideal product* `I·G'` is the smallest
sheaf submodule of `G'` containing every local product `a • m` of a section `a` of `I` with a
section `m` of `G'`.

Its basic property is that the kernel of the structure map annihilates it: a section of `I·G'`
is locally a sum of products `a • m`, and the kernel is `I`, which is square zero. Consequently
`I·G'` is a direct image: by the essential-image criterion of Stacks 08M3 it is
`i_*K` for a sheaf of `O'`-modules `K`, and `K` together with that identification is
`idealProductModule`.

## Main definitions

* `Deformation.ToposThickening.idealProductSubmodule`: the sheaf submodule `I·G'` of `G'`.
* `Deformation.ToposThickening.idealProductModule`: the descent of `I·G'` to the source topos,
  specified by its direct image.

## Main results

* `Deformation.ToposThickening.FirstOrderThickening.smul_mem_idealProductSubmodule_eq_zero`: a
  section of the structure-map kernel annihilates `I·G'`.
* `Deformation.ToposThickening.essImage_idealProductSubmodule`: `I·G'` is in the essential image
  of the direct image on modules.

## Implementation notes

The annihilation statement is proved through an auxiliary submodule: the sections of `G'` killed
by every kernel section after every restriction. That submodule is a *sheaf* submodule, it
contains every product `a • m` because the ideal is square zero, and it therefore contains
`I·G'`, which is the infimum of the sheaf submodules containing those products. Evaluating the
membership at the identity morphism gives the statement.

The direct image used here is
`AlgebraicGeometry.RingedToposHom.pushforwardModules`, the direct image on modules of the
two-field morphism of ringed topoi of Stacks 01D3 part (2), because that is the functor the
essential-image criterion of Stacks 08M3 is stated for
(`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`).
It is a different *factorization* of the direct image from
`Stacks.Sheaves.RingedToposModules.pushforwardModules`, which carries the `03D6 "part (1)"`
attribute and is the right adjoint of
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`; the two agree up to
isomorphism but no declaration relates them.

Neither statement below needs a sheafification hypothesis on either site: the essential-image
criterion of Stacks 08M3 does not, and the ideal product is an infimum of sheaf submodules rather
than a sheafification. A direct transcription of the source would carry
`HasWeakSheafify X.J AddCommGrpCat` and
`X.J.WEqualsLocallyBijective AddCommGrpCat` throughout its variable block, so `idealProductModule`
here is stated at strictly greater generality than that transcription.

## References

* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u v' u' w

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {i : RingedToposHom X Y}

/-- The sheaf submodule `I·G'` of `G'` generated locally by the products of a section of the
square-zero ideal with a section of `G'`: the infimum of the sheaf submodules containing all
such products. -/
noncomputable def idealProductSubmodule (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) : G'.Submodule :=
  sInf { N : G'.Submodule |
    ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (m : G'.val.obj U),
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
        hi.incl.val.app U a) • m ∈ N.obj U }

/-- The presheaf submodule of sections of `G'` annihilated, after every restriction, by every
section of the kernel of the structure map. -/
private noncomputable def kernelAnnihilatorPresheafSubmodule
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    G'.val.Submodule where
  obj U :=
    { carrier := {m | ∀ (V : Y.Cᵒᵖ) (f : U ⟶ V)
        (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V),
        i.fSharp.hom.app V a = 0 → a • G'.val.map f m = 0}
      zero_mem' := by
        intro V f a _
        change a • (G'.val.presheaf.map f).hom 0 = 0
        rw [map_zero, smul_zero]
      add_mem' := by
        intro x y hx hy V f a ha
        change a • G'.val.map f (x + y) = 0
        rw [(G'.val.map f).hom.map_add, smul_add, hx V f a ha, hy V f a ha, add_zero]
      smul_mem' := by
        intro r s hs V f a ha
        change a • G'.val.map f (r • s) = 0
        rw [G'.val.map_smul, smul_smul]
        let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V) :=
          inferInstanceAs (CommRing (Y.O.obj.obj V))
        rw [mul_comm a, ← smul_smul, hs V f a ha, smul_zero] }
  map := by
    intro U V f s hs W g a ha
    change a • G'.val.map g (G'.val.map f s) = 0
    rw [← G'.val.map_comp_apply]
    exact hs W (f ≫ g) a ha

/-- A section in the presheaf annihilator is killed by every section of the kernel over the same
object. -/
private lemma smul_eq_zero_of_mem_kernelAnnihilatorPresheafSubmodule
    {G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} {U : Y.Cᵒᵖ}
    {m : G'.val.obj U} (hm : m ∈ (kernelAnnihilatorPresheafSubmodule (i := i) G').obj U)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) (ha : i.fSharp.hom.app U a = 0) :
    a • m = 0 := by
  have hz := hm U (𝟙 U) a ha
  simp only [PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
    ModuleCat.restrictScalarsId'App_inv_apply] at hz
  let e := ModuleCat.restrictScalarsId'App
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map (𝟙 U)).hom
    (congrArg RingCat.Hom.hom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map_id U))
    (G'.val.obj U)
  exact congrArg (fun x => e.hom x) hz

/-- The sheaf submodule of sections of `G'` annihilated, after every restriction, by every
section of the kernel of the structure map. -/
private noncomputable def kernelAnnihilatorSubmodule (_hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) : G'.Submodule := by
  refine ⟨kernelAnnihilatorPresheafSubmodule (i := i) G', ?_⟩
  intro U s hs V f a ha
  let S := (kernelAnnihilatorPresheafSubmodule (i := i) G').toSubfunctor.sieveOfSection s
  have hG : Presieve.IsSheaf Y.J
      (G'.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SheafOfModules.isSheaf G'))
  refine (hG (S.pullback f.unop) (Y.J.pullback_stable f.unop hs)).isSeparatedFor.ext ?_
  intro W g hg
  change G'.val.restrictₛₗ g.op (a • G'.val.map f s) = G'.val.restrictₛₗ g.op 0
  rw [map_zero]
  refine (G'.val.restrictₛₗ g.op).map_smulₛₗ a _ |>.trans ?_
  change ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g.op).hom a •
    G'.val.map g.op (G'.val.map f s) = 0
  let t : (G'.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w}).obj
      (Opposite.op W) :=
    (G'.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w}).map (g ≫ f.unop).op s
  have hmem : t ∈ (kernelAnnihilatorPresheafSubmodule (i := i) G').toSubfunctor.obj
      (Opposite.op W) := by
    simpa [t, S, Subfunctor.sieveOfSection, Sieve.pullback] using hg
  have hker : i.fSharp.hom.app (Opposite.op W)
      (((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g.op).hom a) = 0 := by
    let a' : Y.O.obj.obj V := a
    have ha' : (i.fSharp.hom.app V) a' = 0 := by simpa [a'] using ha
    have hz := congrArg (fun q => q.hom a') (i.fSharp.hom.naturality g.op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hz
    rw [ha', map_zero] at hz
    exact hz
  have hz := smul_eq_zero_of_mem_kernelAnnihilatorPresheafSubmodule
    (m := t) hmem _ hker
  have ht : t = G'.val.presheaf.map g.op (G'.val.presheaf.map f s) := by
    change G'.val.presheaf.map (f ≫ g.op) s = _
    have hfg : (g ≫ f.unop).op = f ≫ g.op := by simp
    rw [← hfg]
    exact G'.val.map_comp_apply f g.op s
  rw [ht] at hz
  exact hz

private lemma idealProductSubmodule_le_kernelAnnihilator (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    idealProductSubmodule hi G' ≤ kernelAnnihilatorSubmodule hi G' := by
  apply sInf_le
  intro U a m
  simp only [kernelAnnihilatorSubmodule]
  change ∀ (V : Y.Cᵒᵖ) (f : U ⟶ V) (b : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V),
      i.fSharp.hom.app V b = 0 →
        b • G'.val.map f ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
          hi.incl.val.app U a) • m) = 0
  intro V f b hb
  obtain ⟨c, hc⟩ := (hi.kernel V b).mp hb
  have hincl : G'.val.map f
      ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a) • m) =
      ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V from
      hi.incl.val.app V ((hi.I.val.map f) a)) • G'.val.map f m) := by
    rw [G'.val.map_smul]
    congr 1
    change ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map f).hom (hi.incl.val.app U a) =
      hi.incl.val.app V ((hi.I.val.map f) a)
    have hn := congrArg (fun q => q a) (hi.incl.val.naturality f)
    change (ConcreteCategory.hom (hi.incl.val.app V))
        ((ConcreteCategory.hom (hi.I.val.map f)) a) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map f).hom (hi.incl.val.app U a) at hn
    exact hn.symm
  rw [hincl, smul_smul]
  have hcomm : b * (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V from
      hi.incl.val.app V ((hi.I.val.map f) a)) = 0 := by
    rw [← hc]
    exact hi.square_zero V c ((hi.I.val.map f) a)
  rw [hcomm, zero_smul]

/-- **The kernel of the structure map annihilates the ideal product.** A section of the kernel
of `i♯` kills every section of `I·G'`, because the kernel is the square-zero ideal `I`. -/
theorem FirstOrderThickening.smul_mem_idealProductSubmodule_eq_zero
    (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (U : Y.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (ha : i.fSharp.hom.app U a = 0) (m : G'.val.obj U)
    (hm : m ∈ (idealProductSubmodule hi G').obj U) : a • m = 0 := by
  have hmA : m ∈ (kernelAnnihilatorSubmodule hi G').obj U :=
    idealProductSubmodule_le_kernelAnnihilator hi G' U hm
  exact smul_eq_zero_of_mem_kernelAnnihilatorPresheafSubmodule hmA a ha

/-- **The ideal product is a direct image.** By the essential-image criterion of Stacks 08M3 the
sheaf submodule `I·G'`, being annihilated by the ideal of the thickening, is the direct image of
a sheaf of modules on the source topos. -/
theorem essImage_idealProductSubmodule (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    i.pushforwardModules.essImage (idealProductSubmodule hi G').toSheafOfModules := by
  refine (ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates
    hi.closedRingedImmersion (idealProductSubmodule hi G').toSheafOfModules).2
    fun U a ha m => Subtype.ext ?_
  have haKer : a ∈ RingHom.ker ((hi.closedRingedImmersion.hom.fSharp.hom.app U).hom) := by
    rwa [← ClosedRingedImmersion.ideal_obj hi.closedRingedImmersion U]
  exact hi.smul_mem_idealProductSubmodule_eq_zero G' U a (RingHom.mem_ker.mp haKer)
    m.val m.property

/-- The descent of the ideal product `I·G'` to the source topos: a sheaf of `O'`-modules whose
direct image is `I·G'`. -/
noncomputable def idealProductModule (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    { K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) //
      Nonempty (i.pushforwardModules.obj K ≅
        (idealProductSubmodule hi G').toSheafOfModules) } :=
  Classical.choice
    ⟨⟨(essImage_idealProductSubmodule hi G').witness,
      ⟨(essImage_idealProductSubmodule hi G').getIso⟩⟩⟩

end Deformation.ToposThickening

end
