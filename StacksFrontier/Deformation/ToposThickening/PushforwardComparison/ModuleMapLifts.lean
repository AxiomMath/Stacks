module

public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.IdealProduct
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ModulesAbelian
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Lifts of a map of modules across a first order thickening

Let `i : (Sh(C), O') ⟶ (Sh(D), O)` be a first order thickening of ringed topoi with square-zero
ideal `I`, let `F'` and `G'` be sheaves of `O`-modules and let
`φ : i^*F' ⟶ i^*G'` be a map of their pullbacks. Stacks 08MP asserts that if `φ` lifts to a map
`F' ⟶ G'` at all, then the set of its lifts is a principal homogeneous space under the group of
maps `i^*F' ⟶ I·G'`, where `I·G'` is read on the source topos as
`Deformation.ToposThickening.idealProductModule`, and that translation is addition of the
corresponding map into the ideal product followed by its inclusion into `G'`.

## Main definitions

* `Deformation.ToposThickening.ModuleMapLift`: the lifts of a prescribed map of pullbacks.

## Main results

* `Deformation.ToposThickening.idealProductHomEquiv`: maps from the pullback of `F'` to the
  descent of the ideal product are the maps from `F'` into the ideal product.
* `Deformation.ToposThickening.moduleMapLift_torsor`: **Stacks 08MP**, the principal homogeneous
  space of lifts, with its translation formula.

## Implementation notes

The argument is the one of the source, read through the adjunction: a lift of `φ` is a preimage of
`φ` under the additive map `F' ⟶ G' ↦ i^*F' ⟶ i^*G'`, so the fibre is a torsor under the kernel as
soon as it is nonempty. Two facts identify that kernel with the maps into the ideal product.

A map `f : F' ⟶ G'` has `i^*f = 0` exactly when `f` composed with the unit of the adjunction is
zero, the adjunction being additive; and a map killed by the unit factors through the ideal
product. That last step — `idealProductSubmodule_factors_through` — is where the Stacks 08M3
essential-image criterion enters: the cokernel of `I·G' ⟶ G'` is annihilated by the ideal of the
thickening, hence is a direct image, hence the unit is an isomorphism on it, so `f` composed with
the projection to the cokernel vanishes and `f` lifts to the monomorphism `I·G' ⟶ G'`. In the other
direction, the unit kills `I·G'` itself, which is
`idealProductSubmodule_unit_comp_zero`: the kernel of the unit is a sheaf submodule containing
every product `a • m`, and `I·G'` is the smallest such.

The adjunction used throughout is
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison`, Stacks 03D7 for the
  four-field
morphism of ringed topoi of Stacks 01D3 part (2). Its right adjoint is the direct image the
Stacks 08M3 results are stated for, which is what makes those results applicable here; see
`StacksFrontier/Deformation/ToposThickening/PushforwardComparison/Basic.lean`.

Sheaves of modules on the target of a thickening are an abelian category by
`Deformation.ToposThickening.FirstOrderThickening.abelian`, which is *not* an instance: the
hypotheses of a thickening carry no sheafification condition on the target site, so the abelian
structure has to be transported along an equivalence. For the same reason the local surjectivity
of an epimorphism of sheaves of modules used here is proved from `Balanced` rather than quoted from
`Deformation.ToposThickening.sheafModule_epi_locallySurjective`, which needs
`HasSheafify _ AddCommGrpCat` on the site in question.

## References

* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)

universe v u v' u' w

namespace Deformation.ToposThickening

section Sheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The smallest sheaf submodule containing a presheaf submodule: its sections over `U` are the
sections of the module whose membership in the presheaf submodule holds locally. -/
noncomputable def sheafSubmoduleClosure {M : SheafOfModules.{w} R} (N : M.val.Submodule) :
    M.Submodule := by
  let P := N.toSubfunctor.sheafify J
  let Q : M.val.Submodule :=
    { obj := fun U =>
        { carrier := P.obj U
          zero_mem' := N.toSubfunctor.le_sheafify J U (N.obj U).zero_mem
          add_mem' := by
            intro x y hx hy
            refine J.superset_covering (fun V f hf => ?_) (J.intersection_covering hx hy)
            change M.val.map f.op (x + y) ∈ N.obj (Opposite.op V)
            rw [(M.val.map f.op).hom.map_add]
            exact (N.obj _).add_mem hf.1 hf.2
          smul_mem' := by
            intro r x hx
            refine J.superset_covering (fun V f hf => ?_) hx
            change M.val.map f.op (r • x) ∈ N.obj (Opposite.op V)
            rw [M.val.map_smul]
            exact (N.obj _).smul_mem _ hf }
      map := fun f _ hx => P.map f hx }
  have hM : Presieve.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat.{w}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ M.isSheaf)
  exact ⟨Q, fun U x hx => (P.isSheaf_iff hM).mp (N.toSubfunctor.sheafify_isSheaf hM) U x hx⟩

/-- **An epimorphism of sheaves of modules is locally surjective on sections**, in a balanced
category of sheaves of modules.

`Deformation.ToposThickening.sheafModule_epi_locallySurjective` is the same statement under
`HasSheafify _ AddCommGrpCat` and `WEqualsLocallyBijective`, which the hypotheses of a first order
thickening do not provide on the target site. Here the image of the map is replaced by its sheaf
closure, which receives the map and is contained in the target; the induced map is therefore an
epimorphism, hence an isomorphism, so every section of the target is locally in the image. -/
theorem epi_isLocallySurjective_of_balanced [Balanced (SheafOfModules.{w} R)]
    {M N : SheafOfModules.{w} R} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) := by
  let P : N.val.Submodule :=
    { obj := fun U => (f.val.app U).hom.range
      map := by
        rintro U V g _ ⟨x, rfl⟩
        exact ⟨M.val.map g x, PresheafOfModules.naturality_apply f.val g x⟩ }
  let Q := sheafSubmoduleClosure P
  let q : M ⟶ Q.toSheafOfModules := ⟨{
    app := fun U => ModuleCat.ofHom ((f.val.app U).hom.codRestrict (Q.obj U)
      (fun x => P.toSubfunctor.le_sheafify J U ⟨x, rfl⟩))
    naturality := by
      intro U V g
      ext x
      exact Subtype.ext (PresheafOfModules.naturality_apply f.val g x) }⟩
  have hq : q ≫ Q.ι = f := by ext U x; rfl
  have : Epi Q.ι := epi_of_epi_fac hq
  have : IsIso Q.ι := isIso_of_mono_of_epi _
  refine ⟨fun {U} x => ?_⟩
  let y := (inv Q.ι).val.app (Opposite.op U) x
  have hy : (Q.ι.val.app (Opposite.op U)) y = x :=
    congrArg (fun k : N ⟶ N => (k.val.app (Opposite.op U)).hom x) (IsIso.inv_hom_id Q.ι)
  have hm : P.toSubfunctor.sieveOfSection y.val ∈ J U := y.property
  rwa [show y.val = x from hy] at hm

/-- The underlying type-valued presheaf of a sheaf of modules is a sheaf of types. -/
private theorem isSheaf_forget_presheaf (M : SheafOfModules.{w} R) :
    Presieve.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat.{w}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ _ _ M.isSheaf)

end Sheafification

section Torsor

/-- **The fibre of an additive map over a point, as a torsor under the kernel.** If `k` is an
injective additive map whose image is exactly the kernel of `f`, then the fibre of `f` over `c`,
when nonempty, is a principal homogeneous space under the source of `k`, with translation given by
adding `k a`. -/
theorem addTorsor_fiber_of_exact {A B D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (k : A →+ B) (f : B →+ D) (hk : Function.Injective k)
    (hex : ∀ b, f b = 0 ↔ ∃ a, k a = b) (c : D) (hne : Nonempty {b : B // f b = c}) :
    ∃ t : AddTorsor A {b : B // f b = c},
      ∀ a p, (t.vadd a p).val = p.val + k a := by
  classical
  have hzero (a : A) : f (k a) = 0 := (hex _).mpr ⟨a, rfl⟩
  have hd (p q : {b : B // f b = c}) : ∃ a, k a = p.val - q.val :=
    (hex _).mp (by rw [map_sub, p.property, q.property, sub_self])
  choose d hd using hd
  exact ⟨
    { vadd := fun a p => ⟨p.val + k a, by rw [map_add, hzero, add_zero, p.property]⟩
      zero_vadd := fun p => Subtype.ext (by
        change p.val + k 0 = p.val
        rw [map_zero, add_zero])
      add_vadd := fun a b p => Subtype.ext (by
        change p.val + k (a + b) = (p.val + k b) + k a
        rw [map_add]
        abel)
      vsub := d
      nonempty := hne
      vsub_vadd' := fun p q => Subtype.ext (by
        change q.val + k (d p q) = p.val
        rw [hd]
        abel)
      vadd_vsub' := fun a p => hk (by
        change k (d ⟨p.val + k a, _⟩ p) = k a
        rw [hd]
        change p.val + k a - p.val = k a
        exact add_sub_cancel_left _ _) }, fun _ _ => rfl⟩

end Torsor

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

/-- The pullback of sheaves of modules along a morphism of ringed topoi is additive: it is a left
adjoint, and its right adjoint preserves binary products. -/
theorem pullbackModules_additive :
    (i.toRingedToposModulesHom.pullbackModules).Additive := by
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  have := adj.isRightAdjoint
  have : i.pushforwardModules.Additive := Functor.additive_of_preserves_binary_products _
  exact adj.left_adjoint_additive

/-- **The unit of the adjunction kills the ideal product.** The kernel of the unit at `G'` is a
sheaf submodule of `G'` containing every product of a section of the square-zero ideal with a
section of `G'`, and `I·G'` is the smallest such. -/
theorem idealProductSubmodule_unit_comp_zero (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (idealProductSubmodule hi G').ι ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app G' = 0
      := by
  let η := i.pullbackAdjPushforwardModulesViaComparison.unit.app G'
  let H := i.pushforwardModules.obj
    ((i.toRingedToposModulesHom.pullbackModules).obj G')
  let P : G'.val.Submodule :=
    { obj := fun U => (η.val.app U).hom.ker
      map := by
        intro U V f x hx
        change η.val.app V (G'.val.map f x) = 0
        exact (PresheafOfModules.naturality_apply η.val f x).trans
          ((congrArg (fun z => H.val.map f z) (LinearMap.mem_ker.mp hx)).trans (map_zero _)) }
  let N : G'.Submodule :=
    { toSubmodule := P
      isSheaf := by
        intro U x hx
        let S := P.toSubfunctor.sieveOfSection x
        refine (isSheaf_forget_presheaf H S hx).isSeparatedFor.ext ?_
        intro V f hf
        have hmem : η.val.app (Opposite.op V) ((G'.val.map f.op) x) = 0 :=
          LinearMap.mem_ker.mp (show (G'.val.map f.op) x ∈ P.obj (Opposite.op V) from hf)
        change (H.val.presheaf.map f.op) ((η.val.app U).hom x) =
          (H.val.presheaf.map f.op) 0
        have hnat := PresheafOfModules.naturality_apply η.val f.op x
        change η.val.app (Opposite.op V) ((G'.val.map f.op) x) =
          (H.val.presheaf.map f.op) ((η.val.app U).hom x) at hnat
        rw [← hnat, hmem]
        exact (map_zero (ConcreteCategory.hom (H.val.presheaf.map f.op))).symm }
  have hN : N ∈ { Q : G'.Submodule |
      ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (m : G'.val.obj U),
        (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a) •
          m ∈ Q.obj U } := by
    intro U a m
    let r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U := hi.incl.val.app U a
    have ha : (i.structureRingMap.hom.app U).hom r = 0 := by
      change (i.fSharp.hom.app U).hom (hi.incl.val.app U a) = 0
      exact (hi.kernel U (hi.incl.val.app U a)).2 ⟨a, rfl⟩
    change (η.val.app U).hom (r • m) = 0
    rw [map_smul]
    change (i.structureRingMap.hom.app U).hom r •
      (show (Stacks.Sheaves.ToposPushforward.pushforwardModuleFunctor i.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        ((i.toRingedToposModulesHom.pullbackModules).obj G') |>.val.obj U from
          (η.val.app U).hom m) = 0
    rw [ha, zero_smul]
  have hle : idealProductSubmodule hi G' ≤ N := sInf_le hN
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  change (η.val.app U).hom ((idealProductSubmodule hi G').ι.val.app U m) = 0
  exact LinearMap.mem_ker.mp (hle U m.property)

/-- **A map killed by the unit factors through the ideal product.** The cokernel of the inclusion
`I·G' ⟶ G'` is annihilated by the ideal of the thickening, so by the essential-image criterion of
Stacks 08M3 it is a direct image, and the unit of the adjunction is an isomorphism on it. A map
`f : F' ⟶ G'` whose composite with the unit vanishes therefore has zero composite with the
projection to the cokernel, and so factors through the monomorphism `I·G' ⟶ G'`. -/
theorem idealProductSubmodule_factors_through (hi : FirstOrderThickening i)
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (f : F' ⟶ G')
    (hf : f ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app G' = 0) :
    ∃ g : F' ⟶ (idealProductSubmodule hi G').toSheafOfModules,
      f = g ≫ (idealProductSubmodule hi G').ι := by
  let hab := hi.abelian
  let M := idealProductSubmodule hi G'
  let Q := cokernel M.ι
  let q := cokernel.π M.ι
  have hkill : ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (m : G'.val.obj U),
      (q.val.app U).hom
        ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
          hi.incl.val.app U a) • m) = 0 := by
    intro U a m
    let x : G'.val.obj U :=
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a) • m
    have hx : x ∈ M.obj U := by
      change x ∈ (sInf ((fun N : G'.Submodule => N.toSubmodule) ''
        {N : G'.Submodule | ∀ (V : Y.Cᵒᵖ) (b : hi.I.val.obj V) (n : G'.val.obj V),
          (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V from
            hi.incl.val.app V b) • n ∈ N.obj V})).obj U
      simp only [PresheafOfModules.Submodule.sInf_obj, Submodule.mem_iInf]
      intro N hN
      obtain ⟨N', hN', rfl⟩ := hN
      exact hN' U a m
    have hc : (M.ι.val.app U) ≫ q.val.app U = 0 :=
      congrArg (fun k : M.toSheafOfModules ⟶ Q => k.val.app U) (cokernel.condition M.ι)
    exact congrArg (fun k : M.toSheafOfModules.val.obj U ⟶ Q.val.obj U =>
      ModuleCat.Hom.hom k ⟨x, hx⟩) hc
  let S := hi.closedRingedImmersion
  have hQ : ∀ (U : Y.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U),
      a ∈ S.ideal.obj U → ∀ m : Q.val.obj U, a • m = 0 := by
    intro U a ha m
    have haKer : a ∈ RingHom.ker ((S.hom.fSharp.hom.app U).hom) := by
      rwa [← ClosedRingedImmersion.ideal_obj S U]
    let P := PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
    let fq := P.map q.val
    let Sₘ := Presheaf.imageSieve fq (m : ToType ((P.obj Q.val).obj U))
    have : Epi q := by dsimp [q]; infer_instance
    have hloc : Presheaf.IsLocallySurjective Y.J fq :=
      epi_isLocallySurjective_of_balanced q
    have hcover : Sₘ ∈ Y.J U.unop :=
      Presheaf.imageSieve_mem (J := Y.J) fq (m : ToType ((P.obj Q.val).obj U))
    refine (isSheaf_forget_presheaf Q Sₘ hcover).isSeparatedFor.ext ?_
    intro V g hg
    obtain ⟨x, hx⟩ := hg
    let aV : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V) :=
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g.op).hom a
    have haVker : i.fSharp.hom.app (Opposite.op V) aV = 0 := by
      let a' : Y.O.obj.obj U := a
      have ha' : (i.fSharp.hom.app U) a' = 0 := (RingHom.mem_ker).mp haKer
      have hz := congrArg (fun r => r.hom a') (i.fSharp.hom.naturality g.op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hz
      rwa [ha', map_zero] at hz
    obtain ⟨bV, hbV⟩ := (hi.kernel (Opposite.op V) aV).mp haVker
    let x' : G'.val.obj (Opposite.op V) := x
    have hx' : (q.val.app (Opposite.op V)).hom x' = Q.val.map g.op m := hx
    have hmod : (q.val.app (Opposite.op V)).hom (aV • x') = 0 := by
      rw [← hbV]
      exact hkill (Opposite.op V) bV x'
    change (Q.val.map g.op).hom (a • m) = (Q.val.map g.op).hom 0
    rw [map_zero, Q.val.map_smul, ← hx']
    change aV • (q.val.app (Opposite.op V)).hom x' = 0
    exact ((q.val.app (Opposite.op V)).hom.map_smul aV x').symm.trans hmod
  have hEss := (ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates S Q).2 hQ
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  have ff := (ClosedRingedImmersion.pushforwardModules_fullyFaithful S).some
  have : i.pushforwardModules.Faithful := ff.faithful
  have : i.pushforwardModules.Full := ff.full
  have hη : IsIso (adj.unit.app Q) := adj.isIso_unit_app_iff_mem_essImage.2 hEss
  have hq : f ≫ q = 0 := by
    have hn : q ≫ adj.unit.app Q =
        adj.unit.app G' ≫
          (i.toRingedToposModulesHom.pullbackModules ⋙ i.pushforwardModules).map q := by
      simpa only [Functor.id_map] using adj.unit.naturality q
    exact (cancel_mono (adj.unit.app Q)).1 (by
      rw [Category.assoc, hn, ← Category.assoc, hf, zero_comp, zero_comp])
  exact ⟨Abelian.monoLift M.ι f hq, (Abelian.monoLift_comp M.ι f hq).symm⟩

/-- The lifts of a prescribed map of pullbacks: the maps `F' ⟶ G'` whose pullback is `φ`. -/
abbrev ModuleMapLift (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (φ : (i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
      (i.toRingedToposModulesHom.pullbackModules).obj G') :
    Type _ :=
  { φ' : F' ⟶ G' //
    (i.toRingedToposModulesHom.pullbackModules).map φ' = φ }

/-- **Maps into the descended ideal product are maps into the ideal product.** The adjunction of
Stacks 03D7 identifies the maps from the pullback of `F'` to the descent of `I·G'` with the maps
from `F'` to its direct image, which is `I·G'` itself. -/
noncomputable def idealProductHomEquiv (hi : FirstOrderThickening i)
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (((i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
        (idealProductModule hi G').val) ≃+
      (F' ⟶ (idealProductSubmodule hi G').toSheafOfModules)) :=
  letI : (i.toRingedToposModulesHom.pullbackModules).Additive := pullbackModules_additive
  let e := (idealProductModule hi G').property.some
  (i.pullbackAdjPushforwardModulesViaComparison.homAddEquiv F' (idealProductModule hi G').val).trans
    { toFun := fun g => g ≫ e.hom
      invFun := fun g => g ≫ e.inv
      left_inv := fun g =>
        (Category.assoc g e.hom e.inv).trans
          ((congrArg (fun m => g ≫ m) e.hom_inv_id).trans (Category.comp_id g))
      right_inv := fun g =>
        (Category.assoc g e.inv e.hom).trans
          ((congrArg (fun m => g ≫ m) e.inv_hom_id).trans (Category.comp_id g))
      map_add' := fun g h => Preadditive.add_comp _ _ _ g h e.hom }

/-- **Stacks 08MP.** If a map of pullbacks across a first order thickening has a lift, then its
lifts form a principal homogeneous space under the maps from the pullback of `F'` to the descent of
the ideal product `I·G'`, with translation given by adding the corresponding map into `I·G'`
followed by its inclusion into `G'`. -/
@[stacks 08MP]
theorem moduleMapLift_torsor (hi : FirstOrderThickening i)
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (φ : (i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
      (i.toRingedToposModulesHom.pullbackModules).obj G')
    (h : Nonempty (ModuleMapLift F' G' φ)) :
    ∃ t : AddTorsor
        ((i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
          (idealProductModule hi G').val)
        (ModuleMapLift F' G' φ),
      ∀ (α : (i.toRingedToposModulesHom.pullbackModules).obj F' ⟶ (idealProductModule hi G').val)
        (c : ModuleMapLift F' G' φ),
        (t.vadd α c).val = c.val +
          idealProductHomEquiv hi F' G' α ≫ (idealProductSubmodule hi G').ι := by
  let L := i.toRingedToposModulesHom.pullbackModules
  have hadd : L.Additive := pullbackModules_additive
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let M := idealProductSubmodule hi G'
  let e := idealProductHomEquiv hi F' G'
  let k := (Preadditive.compHom.flip M.ι).comp e.toAddMonoidHom
  have heta (g : F' ⟶ G') :
      adj.homEquiv F' (L.obj G') (L.map g) = g ≫ adj.unit.app G' :=
    ((congrArg (adj.homEquiv F' (L.obj G')) (Category.comp_id (L.map g)).symm).trans
      (adj.homEquiv_naturality_left g (𝟙 _))).trans
      (congrArg (fun m => g ≫ m) (adj.homEquiv_id G'))
  have hker (g : F' ⟶ G') : L.map g = 0 ↔ g ≫ adj.unit.app G' = 0 := by
    rw [← heta]
    exact (adj.homAddEquiv F' (L.obj G')).map_eq_zero_iff.symm
  have hex (g : F' ⟶ G') : L.mapAddHom g = 0 ↔ ∃ a, k a = g := by
    change L.map g = 0 ↔ _
    rw [hker]
    refine ⟨fun hg => ?_, ?_⟩
    · obtain ⟨g', hg'⟩ := idealProductSubmodule_factors_through hi F' G' g hg
      exact ⟨e.symm g', by change e (e.symm g') ≫ M.ι = g; rw [e.apply_symm_apply, hg']⟩
    · rintro ⟨a, rfl⟩
      change (e a ≫ M.ι) ≫ adj.unit.app G' = 0
      rw [Category.assoc, idealProductSubmodule_unit_comp_zero hi G', comp_zero]
  exact addTorsor_fiber_of_exact k L.mapAddHom
    (fun _ _ hab => e.injective ((cancel_mono M.ι).mp hab)) hex φ h

end Deformation.ToposThickening

end
