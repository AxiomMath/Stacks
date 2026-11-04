module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# A square-zero ideal of sheaves of modules, read through a transport

Let `Φ : Sh(D, K) ⥤ Sh(C, J)` be a finite-product-preserving functor between categories of
sheaves of sets — in the application the direct image along a morphism of algebraic spaces —
let `O` be a sheaf of rings on `(D, K)` and let `ι : N ⟶ O` be an ideal of `O`, that is a
morphism of sheaves of `O`-modules into `O` itself.  The inverse image
`Stacks.Sheaves.ToposPullback.pullbackModuleMap` of `ι` along `Φ` is then an ideal of the
transported sheaf of rings `Φ_*O`, and this file transports the three properties such an ideal
is used through:

* it is **injective on sections**;
* every section of `Φ_*O` killed by the transport of a morphism `ρ : O ⟶ Q` whose kernel `ι`
  is lies in its image — the **exactness** of the ideal sequence;
* its image has **square zero** as soon as the image of `ι` does.

The first and third are formal: the sections of the transport of a morphism of sheaves of
modules are the sections functor of `Φ` applied to the underlying morphism of sheaves of sets,
and that functor preserves finite limits as soon as `Φ` does. For the second, sectionwise
exactness makes `ι` an equalizer in `Sh(D, K)` of `ρ` and the zero morphism, which a
finite-limit-preserving functor preserves.

Two comparisons of scalar actions are also proved: the transport commutes with restriction of
scalars, and the transport of an ideal of `O` is linear for the multiplication of `Φ_*O`.

## Main definitions

* `CategoryTheory.Sheaf.preservesFiniteLimits_sectionsFunctor`: sections over a fixed object is
  a left exact functor on sheaves of types.
* `CategoryTheory.Sheaf.forkLift`: the factorization of a fork through a morphism of sheaves of
  types which is sectionwise injective with image the sectionwise equalizer.
* `CategoryTheory.Sheaf.isLimitForkOfForallApp`: **that morphism is an equalizer.**

## Main results

* `CategoryTheory.Sheaf.injective_map_of_forall_app_injective`: a sectionwise injective morphism
  of sheaves of types stays injective after a functor to types preserving pullbacks.
* `CategoryTheory.Sheaf.exists_map_eq_of_isLimitFork`: **the exactness transports**: after a
  finite-limit-preserving functor to types, every element of the equalizer of the two images is
  in the image of the equalizing morphism.
* `CategoryTheory.Sheaf.mul_map_eq_zero_of_mul_app_eq_zero`: **the square-zero property
  transports.**  The product of two sections in the image of a transported ideal vanishes, in
  the ring structure transported along the functor.
* `Stacks.Sheaves.ToposPullback.smul_pullbackModuleObj_restrictScalars`: the transport of a
  restriction of scalars is the restriction of scalars of the transport, on sections.
* `Stacks.Sheaves.ToposPullback.mul_app_pullbackModuleMap`: the transport of an ideal of `O` is
  linear over `Φ_*O` for its own multiplication.
* `Stacks.Sheaves.ToposPullback.smul_restrictScalars_pullbackModuleObj`: the action of a base
  sheaf of rings mapping into `Φ_*O'` on the transport of an `O'`-module is the action of any
  section of `Φ_*O` with the same image.
* `Stacks.Sheaves.ToposPullback.injective_app_pullbackModuleMap`,
  `Stacks.Sheaves.ToposPullback.exists_app_pullbackModuleMap_eq` and
  `Stacks.Sheaves.ToposPullback.mul_app_pullbackModuleMap_eq_zero`: the three transport
  statements read at the transported morphism itself.

## Implementation notes

The transporting functor `Φ` is given only on sheaves of sets, where there is no zero object
and no kernel. The kernel of an additive map of sheaves of rings is therefore expressed as the
equalizer of that map and the zero generalized element `CategoryTheory.Sheaf.hom_ringZero_eq`
of the same shape, a morphism of sheaves of sets.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2), the inverse image of a
  sheaf of modules.
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3), the kernel ideal of a
  closed immersion of topoi.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf CategoryTheory.Functor

universe t ww ww' vv uu vv' uu'

namespace CategoryTheory.Sheaf

variable {C : Type uu} [Category.{vv} C] {J : GrothendieckTopology C}

/-- Sections of a sheaf of types over a fixed object is a left exact functor. -/
instance preservesFiniteLimits_sectionsFunctor (V : Cᵒᵖ) :
    PreservesFiniteLimits (sectionsFunctor.{ww} J V) := by
  delta sectionsFunctor
  exact Limits.comp_preservesFiniteLimits _ _

variable {N L Q : Sheaf J (Type ww)} {ι : N ⟶ L} {ρ σ : L ⟶ Q}

/-- A sectionwise injective morphism of sheaves of types stays injective after a functor to types
which preserves finite limits. -/
theorem injective_map_of_forall_app_injective
    (h : ∀ X : Cᵒᵖ, Function.Injective (ι.hom.app X))
    (P : Sheaf J (Type ww) ⥤ Type t) [PreservesFiniteLimits P] :
    Function.Injective (P.map ι) :=
  have := Sheaf.mono_of_injective ι h
  have := CategoryTheory.preserves_mono_of_preservesLimit P ι
  CategoryTheory.injective_of_mono (P.map ι)

section Fork

variable (hinj : ∀ X : Cᵒᵖ, Function.Injective (ι.hom.app X))
  (hsurj : ∀ (X : Cᵒᵖ) (l : L.obj.obj X), ρ.hom.app X l = σ.hom.app X l →
    ∃ n, ι.hom.app X n = l)

/-- The two morphisms of a fork agree on each section of its leg. -/
theorem fork_condition_app (c : Fork ρ σ) (X : Cᵒᵖ) (x : c.pt.obj.obj X) :
    ρ.hom.app X (c.ι.hom.app X x) = σ.hom.app X (c.ι.hom.app X x) :=
  ConcreteCategory.congr_hom
    (congrArg (fun m : c.pt ⟶ Q => m.hom.app X) c.condition) x

include hinj hsurj

/-- The chosen factorization of a fork through `ι`. -/
def forkLift (c : Fork ρ σ) : c.pt ⟶ N :=
  unaryOpHom (A := c.pt) (E := N)
    (fun X x => (hsurj X (c.ι.hom.app X x) (fork_condition_app c X x)).choose)
    (fun {X Y} g x => hinj Y (by
      rw [NatTrans.naturality_apply ι.hom g,
        (hsurj X (c.ι.hom.app X x) (fork_condition_app c X x)).choose_spec,
        (hsurj Y (c.ι.hom.app Y (c.pt.obj.map g x))
          (fork_condition_app c Y (c.pt.obj.map g x))).choose_spec,
        NatTrans.naturality_apply c.ι.hom g]))

/-- The factorization `forkLift` of a fork through `ι`, composed with `ι`, is the leg of the
fork. -/
theorem forkLift_comp (c : Fork ρ σ) : forkLift hinj hsurj c ≫ ι = c.ι :=
  Sheaf.hom_ext_sections fun X x =>
    (hsurj X (c.ι.hom.app X x) (fork_condition_app c X x)).choose_spec

/-- A sectionwise injective morphism of sheaves of types whose image on sections is the
sectionwise equalizer of `ρ` and `σ` is an equalizer of `ρ` and `σ`. -/
def isLimitForkOfForallApp (h : ι ≫ ρ = ι ≫ σ) : IsLimit (Fork.ofι ι h) :=
  haveI := Sheaf.mono_of_injective ι hinj
  Fork.IsLimit.mk _ (fun c => forkLift hinj hsurj c)
    (fun c => forkLift_comp hinj hsurj c)
    (fun c k hk => (cancel_mono ι).1
      ((hk : k ≫ ι = c.ι).trans (forkLift_comp hinj hsurj c).symm))

end Fork

/-- After a finite-limit-preserving functor `P` to types, every element of the equalizer of
`P.map ρ` and `P.map σ` lies in the image of `P.map ι`, for `ι` an equalizer of `ρ` and `σ`. -/
theorem exists_map_eq_of_isLimitFork (h : ι ≫ ρ = ι ≫ σ) (hlim : IsLimit (Fork.ofι ι h))
    (P : Sheaf J (Type ww) ⥤ Type t) [PreservesFiniteLimits P]
    (m : P.obj L) (hm : P.map ρ m = P.map σ m) :
    ∃ n, P.map ι n = m := by
  have hP := isLimitForkMapOfIsLimit P h hlim
  obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hP (↾(fun _ : PUnit.{t + 1} => m))
    (by ext _; exact hm)
  exact ⟨ConcreteCategory.hom l PUnit.unit, by simpa using ConcreteCategory.congr_hom hl PUnit.unit⟩

variable [J.HasSheafCompose (forget RingCat.{ww})]

/-- If the product of any two sections of the image of `g : Z ⟶ ringSheaf R` vanishes, then after
a finite-product-preserving functor `P` to types the product of the images under `P.map g` of any
two elements vanishes, for the ring structure `ringObjRing R P`. -/
theorem mul_map_eq_zero_of_mul_app_eq_zero {R : Sheaf J RingCat.{ww}} {Z : Sheaf J (Type ww)}
    (g : Z ⟶ ringSheaf R)
    (hg : ∀ (X : Cᵒᵖ) (a b : Z.obj.obj X),
      (show ToType (R.obj.obj X) from g.hom.app X a) *
        (show ToType (R.obj.obj X) from g.hom.app X b) = 0)
    (P : Sheaf J (Type ww) ⥤ Type t) [PreservesFiniteProducts P] (m m' : P.obj Z) :
    letI := ringObjRing R P
    P.map g m * P.map g m' = 0 := by
  let := ringObjRing R P
  have key : ((Limits.prod.fst : Z ⨯ Z ⟶ Z) ≫ g) * ((Limits.prod.snd : Z ⨯ Z ⟶ Z) ≫ g) = 0 := by
    refine hom_ext_sections fun X z => ?_
    rw [sectionsFunctor_map_hom_mul, sectionsFunctor_map_hom_ringZero,
      Functor.map_comp_apply, Functor.map_comp_apply]
    exact hg X _ _
  have h2 := congrArg (fun n => P.map n (Functor.prodObjMk (P := P) m m')) key
  rwa [map_hom_mul P, map_hom_ringZero P, P.map_comp_apply, P.map_comp_apply,
    Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk] at h2

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory.Sheaf Stacks.Sheaves.RingedToposModules

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {O O' : Sheaf K RingCat.{ww'}} (ρ : O ⟶ O') (N : SheafOfModules.{ww'} O')

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- On sections, the action of the transported ring `Φ_*O` on the transport of the restriction
of scalars of `N` along `ρ` is the action through the transport of `ρ`. -/
theorem smul_pullbackModuleObj_restrictScalars (V : Cᵒᵖ)
    (r : (pullbackRingSheaf J Φ O).obj.obj V)
    (m : (pullbackModuleObj J Φ O ((SheafOfModules.restrictScalars ρ).obj N)).val.obj V) :
    r • m = (pullbackRingSheafMap J Φ ρ).hom.app V r •
      (show (pullbackModuleObj J Φ O' N).val.obj V from m) :=
  moduleSMulObj_restrictScalars ρ N (Φ ⋙ CategoryTheory.Sheaf.sectionsFunctor J V) r m

/-- Let `α : R ⟶ Φ_*O'` be a morphism of sheaves of rings, so that the transport `Φ_*N` of an
`O'`-module is an `R`-module by restriction of scalars. A section `r` of `Φ_*O` whose image under
the transport of `ρ : O ⟶ O'` is the image of a section `t` of `R` acts on `Φ_*N` exactly as `t`
does. -/
theorem smul_restrictScalars_pullbackModuleObj
    {R : Sheaf J RingCat.{ww}} (α : R ⟶ pullbackRingSheaf J Φ O') (V : Cᵒᵖ) (t : R.obj.obj V)
    (r : (pullbackRingSheaf J Φ O).obj.obj V)
    (hrt : (pullbackRingSheafMap J Φ ρ).hom.app V r = α.hom.app V t)
    (m : ((SheafOfModules.restrictScalars α).obj
      (pullbackModuleObj J Φ O' N)).val.obj V) :
    t • m =
      r • (show (pullbackModuleObj J Φ O
        ((SheafOfModules.restrictScalars ρ).obj N)).val.obj V from m) :=
  ((CategoryTheory.Sheaf.sectionsFunctor_map_moduleSMulHom R
        ((SheafOfModules.restrictScalars α).obj (pullbackModuleObj J Φ O' N))
        V t m).symm.trans
      ((moduleSMulObj_restrictScalars α (pullbackModuleObj J Φ O' N)
          (CategoryTheory.Sheaf.sectionsFunctor J V) t m).trans
        (CategoryTheory.Sheaf.sectionsFunctor_map_moduleSMulHom _
          (pullbackModuleObj J Φ O' N) V _ m))).trans
    ((congrArg (fun s => s • (show (pullbackModuleObj J Φ O' N).val.obj V from m))
        hrt.symm).trans
      (smul_pullbackModuleObj_restrictScalars J Φ ρ N V r m).symm)

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- On sections, the transport of a morphism `φ : G ⟶ O` of sheaves of `O`-modules is linear for
the multiplication of the transported ring `Φ_*O`. -/
theorem mul_app_pullbackModuleMap {G : SheafOfModules.{ww'} O}
    (φ : G ⟶ SheafOfModules.unit O) (V : Cᵒᵖ)
    (r : (pullbackRingSheaf J Φ O).obj.obj V)
    (m : (pullbackModuleObj J Φ O G).val.obj V) :
    ((pullbackModuleMap J Φ O φ).val.app V).hom (r • m) =
      r * (show ToType ((pullbackRingSheaf J Φ O).obj.obj V) from
        ((pullbackModuleMap J Φ O φ).val.app V).hom m) :=
  ((pullbackModuleMap J Φ O φ).val.app V).hom.map_smul r m

variable {G G' : SheafOfModules.{ww'} O}

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The transport of a morphism of sheaves of modules which is injective on sections is injective
on sections. -/
theorem injective_app_pullbackModuleMap [PreservesFiniteLimits Φ] (φ : G ⟶ G') (V : Cᵒᵖ)
    (hφ : ∀ X : Dᵒᵖ, Function.Injective ((φ.val.app X).hom)) :
    Function.Injective (((pullbackModuleMap J Φ O φ).val.app V).hom) :=
  CategoryTheory.Sheaf.injective_map_of_forall_app_injective
    (ι := (CategoryTheory.Sheaf.moduleSheafFunctor O).map φ) hφ
    (Φ ⋙ CategoryTheory.Sheaf.sectionsFunctor J V)

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The transport of an ideal of `O` whose image has square zero has image of square zero. -/
theorem mul_app_pullbackModuleMap_eq_zero (φ : G ⟶ SheafOfModules.unit O) (V : Cᵒᵖ)
    (hφ : ∀ (X : Dᵒᵖ) (m m' : G.val.obj X),
      (show ToType (O.obj.obj X) from (φ.val.app X).hom m) *
        (show ToType (O.obj.obj X) from (φ.val.app X).hom m') = 0)
    (m m' : (pullbackModuleObj J Φ O G).val.obj V) :
    (show ToType ((pullbackRingSheaf J Φ O).obj.obj V) from
        ((pullbackModuleMap J Φ O φ).val.app V).hom m) *
      (show ToType ((pullbackRingSheaf J Φ O).obj.obj V) from
        ((pullbackModuleMap J Φ O φ).val.app V).hom m') = 0 :=
  CategoryTheory.Sheaf.mul_map_eq_zero_of_mul_app_eq_zero
    ((CategoryTheory.Sheaf.moduleSheafFunctor O).map φ) hφ
    (Φ ⋙ CategoryTheory.Sheaf.sectionsFunctor J V) m m'

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- If `φ : G ⟶ O` is injective on sections, lands in the kernel of `ρ : O ⟶ O'` and has that
kernel for its image, then every section of `Φ_*O` killed by the transport of `ρ` along a left
exact `Φ` is in the image of the transport of `φ`. -/
theorem exists_app_pullbackModuleMap_eq [PreservesFiniteLimits Φ]
    (φ : G ⟶ SheafOfModules.unit O) (ρ : O ⟶ O') (V : Cᵒᵖ)
    (hzero : ∀ (X : Dᵒᵖ) (m : G.val.obj X),
      ρ.hom.app X (show ToType (O.obj.obj X) from (φ.val.app X).hom m) = 0)
    (hinj : ∀ X : Dᵒᵖ, Function.Injective ((φ.val.app X).hom))
    (hex : ∀ (X : Dᵒᵖ) (s : O.obj.obj X), ρ.hom.app X s = 0 →
      ∃ m, (show ToType (O.obj.obj X) from (φ.val.app X).hom m) = s)
    (z : (pullbackRingSheaf J Φ O).obj.obj V)
    (hz : (pullbackRingSheafMap J Φ ρ).hom.app V z = 0) :
    ∃ m : (pullbackModuleObj J Φ O G).val.obj V,
      ((pullbackModuleMap J Φ O φ).val.app V).hom m = z := by
  set g := (CategoryTheory.Sheaf.moduleSheafFunctor O).map φ with hg
  have h : g ≫ (CategoryTheory.sheafCompose K (forget RingCat.{ww'})).map ρ =
      g ≫ (0 : CategoryTheory.Sheaf.ringSheaf O ⟶ CategoryTheory.Sheaf.ringSheaf O') := by
    refine CategoryTheory.Sheaf.hom_ext_sections fun X m => ?_
    have e1 : (CategoryTheory.Sheaf.sectionsFunctor K X).map
          (g ≫ (CategoryTheory.sheafCompose K (forget RingCat.{ww'})).map ρ) m =
        ρ.hom.app X (show ToType (O.obj.obj X) from (φ.val.app X).hom m) :=
      (CategoryTheory.Sheaf.sectionsFunctor K X).map_comp_apply _ _ m
    have e2 : (CategoryTheory.Sheaf.sectionsFunctor K X).map
          (g ≫ (0 : CategoryTheory.Sheaf.ringSheaf O ⟶ CategoryTheory.Sheaf.ringSheaf O')) m =
        0 :=
      ((CategoryTheory.Sheaf.sectionsFunctor K X).map_comp_apply g
          (0 : CategoryTheory.Sheaf.ringSheaf O ⟶ CategoryTheory.Sheaf.ringSheaf O') m).trans
        (CategoryTheory.Sheaf.sectionsFunctor_map_hom_ringZero X _)
    rw [e1, e2, hzero X m]
    rfl
  have hlim := CategoryTheory.Sheaf.isLimitForkOfForallApp (ι := g) hinj
    (fun X l hl => hex X l (hl.trans
      (CategoryTheory.Sheaf.sectionsFunctor_map_hom_ringZero
        (R := O') (Z := CategoryTheory.Sheaf.ringSheaf O) X l))) h
  exact CategoryTheory.Sheaf.exists_map_eq_of_isLimitFork h hlim
    (Φ ⋙ CategoryTheory.Sheaf.sectionsFunctor J V) z
    (hz.trans (CategoryTheory.Sheaf.map_hom_ringZero
      (Φ ⋙ CategoryTheory.Sheaf.sectionsFunctor J V) z).symm)

end Stacks.Sheaves.ToposPullback

end
