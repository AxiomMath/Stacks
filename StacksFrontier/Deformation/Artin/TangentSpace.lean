module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Infinitesimal automorphisms of a field-valued point

Let `p : X ⥤ (fppf sites over S)` be a category fibred in groupoids and let `x₀` be a point
of `X` over `Spec k`. The *infinitesimal automorphisms* of the predeformation category
`𝓕_{𝓧,k,x₀}` at a dual-number object are the automorphisms of the dual-number extension that
restrict to the identity on the special fibre. This file identifies them with the kernel of
the restriction homomorphism from automorphisms of the dual-number object to automorphisms
of `x₀` itself.

## Main results

* `Deformation.Artin.infinitesimalAutomorphisms_equiv_restrictionKernel` — the canonical
  identification of the infinitesimal automorphisms with the kernel of the restriction
  homomorphism, characterized on underlying arrows of `X`.

## Implementation notes

The original category is fibred over the size-bounded big fppf site, whereas the category
of Artinian algebras is covariant; its opposite is cofibered in groupoids. The arrow from
the special fibre to the dual-number object becomes a cofibered pushforward in the
opposite, so its restriction homomorphism is
`Deformation.pushforwardAutomorphismHom`. The kernel is taken literally with
`MonoidHom.ker`, not re-expressed as a separate subgroup; its commuting-square
characterization is `Deformation.mem_relativeInfinitesimalAutomorphisms_iff`. The
equivalence is characterized on underlying arrows by the reversed-arrow description of
predeformation morphisms.

The identification is first proved for any realization of the predeformation category whose
projection is cofibered in groupoids; for the canonical category `predeformationCategory`
that projection is cofibered in groupoids by
`Deformation.Artin.predeformationCategory_isPredeformationCategory` (Stacks 07T5).

## References

* [Stacks Project, Tag 07X0](https://stacks.math.columbia.edu/tag/07X0)
* [Stacks Project, Tag 07T5](https://stacks.math.columbia.edu/tag/07T5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

private theorem residueMap_bijective
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (e : A ≃ₐ[Λ] k) : Function.Bijective (residueMap A) := by
  have hmax : IsLocalRing.maximalIdeal A = ⊥ := by
    ext x
    rw [Ideal.mem_bot, IsLocalRing.mem_maximalIdeal]
    constructor
    · intro hx
      have he : e x = 0 := by
        by_contra hne
        exact hx (by simpa using (isUnit_iff_ne_zero.mpr hne).map e.symm.toRingHom)
      exact e.injective (by simpa using he)
    · rintro rfl
      simp
  constructor
  · intro a b hab
    have hr : IsLocalRing.residue A a = IsLocalRing.residue A b :=
      A.residueEquiv.injective (by simpa [residueMap] using hab)
    have hzero : IsLocalRing.residue A (a - b) = 0 := by
      rw [RingHom.map_sub, hr]
      simp
    have hmem : a - b ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.residue_eq_zero_iff (R := A) (a - b)).mp hzero
    rw [hmax] at hmem
    exact sub_eq_zero.mp (Ideal.mem_bot.mp hmem)
  · intro b
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) (A.residueEquiv.symm b)
    refine ⟨a, ?_⟩
    show A.residueEquiv (IsLocalRing.residue A a) = b
    rw [ha, A.residueEquiv.apply_symm_apply]

/-- Conjugating an endomorphism by the `eqToHom` of an equality is the identity iff it is. -/
private theorem eqToHom_conj_eq_id_iff {C : Type*} [Category C] {a b : C} (w : a = b)
    (h : a ⟶ a) : eqToHom w.symm ≫ h ≫ eqToHom w = 𝟙 b ↔ h = 𝟙 a := by
  subst w
  simp

private noncomputable def residueMapCommRingIso
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (e : A ≃ₐ[Λ] k) : CommRingCat.of A ≅ CommRingCat.of k :=
  (RingEquiv.ofBijective (residueMap A) (residueMap_bijective A e)).toCommRingCatIso


/-- The identification of infinitesimal automorphisms with the kernel of restriction, for any
realization `D` of the predeformation category whose projection is cofibered in groupoids. -/
private theorem infinitesimalAutomorphisms_equiv_restrictionKernel_of_construction
    (B : BigFppfSite.{u})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (hS : B.Contains S) (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS)
    (hpop : IsCofiberedInGroupoids p.op) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : PredeformationConstruction iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀) :
    letI : Category.{max u w} D.carrier := D.category
    ∀ (hD : IsCofiberedInGroupoids D.projection)
      {A₀ Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
      {z₀ : D.projection.Fiber A₀} {zε : D.projection.Fiber Aε}
      (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
      (hpair : IsCanonicalDualNumberPair g e)
      (i : z₀.1 ⟶ zε.1) (hi : D.projection.IsHomLift g i),
      let y := (D.objects zε.1).point
      let xε' : p.op.Fiber (Opposite.op (p.obj y)) := ⟨Opposite.op y, rfl⟩
      let x₀' : p.op.Fiber (Opposite.op (p.obj x₀)) := ⟨Opposite.op x₀, rfl⟩
      let r := (D.objects zε.1).arrow
      let restriction : Aut xε' →* Aut x₀' :=
        pushforwardAutomorphismHom
          (p := p.op) (x' := xε') (x := x₀') hpop
          (p.op.map r.op) r.op (Functor.IsHomLift.map (p := p.op) r.op)
      ∃! E : ↥(infinitesimalAutomorphisms hD g e hpair i hi) ≃*
          ↥(MonoidHom.ker restriction),
        ∀ a, (E a).val.hom.val.unop =
          (D.morphisms zε.1 zε.1 a.val.hom.val).arrow := by
  classical
  intro hD A₀ Aε z₀ zε g e hpair i hi
  let : Category (D.carrier) := D.category
  let y := (D.objects zε.1).point
  let xε' : p.op.Fiber (Opposite.op (p.obj y)) := ⟨Opposite.op y, rfl⟩
  let x₀' : p.op.Fiber (Opposite.op (p.obj x₀)) := ⟨Opposite.op x₀, rfl⟩
  let r := (D.objects zε.1).arrow
  let q := p ⋙ Over.post B.inclusion
  have ⟨i₀, _, _, _, _⟩ := hpair
  let z₀obj := D.objects z₀.1
  let u₀ := eqToHom (congrArg Over.left hx₀).symm
  let v₀ := eqToHom (congrArg Over.left z₀obj.base)
  have hu₀ : IsIso u₀ := by dsimp [u₀]; infer_instance
  have hv₀ : IsIso v₀ := by dsimp [v₀]; infer_instance
  have hA₀ : A₀ = z₀obj.algebra := z₀.2.symm.trans (D.object_projection z₀.1)
  let i₀' : z₀obj.algebra ≃ₐ[Λ] k := hA₀ ▸ i₀
  let : IsIso (CommRingCat.ofHom (residueMap z₀obj.algebra)) :=
    (residueMapCommRingIso z₀obj.algebra i₀').isIso_hom
  have hresSpec : IsIso (Spec.map (CommRingCat.ofHom
      (residueMap z₀obj.algebra))) :=
    inferInstance
  have hbaseEq := z₀obj.arrow_base
  have hu₀f : IsIso (u₀ ≫ (q.map z₀obj.arrow).left) :=
    IsIso.of_isIso_fac_right hbaseEq
  have hleft₀ : IsIso (q.map z₀obj.arrow).left :=
    IsIso.of_isIso_comp_left u₀ _
  have hq₀ : IsIso (q.map z₀obj.arrow) := by
    let : IsIso ((Over.forget S).map (q.map z₀obj.arrow)) := hleft₀
    exact isIso_of_reflects_iso (q.map z₀obj.arrow) (Over.forget S)
  have hp₀ : IsIso (p.map z₀obj.arrow) := by
    let : IsIso ((Over.post B.inclusion).map (p.map z₀obj.arrow)) := hq₀
    exact isIso_of_reflects_iso (p.map z₀obj.arrow) (Over.post B.inclusion)
  have hz₀arrowOp : IsIso z₀obj.arrow.op := by
    let φ := z₀obj.arrow.op
    have hbaseop : IsIso (p.op.map φ) := by
      show IsIso (p.map z₀obj.arrow).op
      infer_instance
    have hstrong : p.op.IsStronglyCocartesian (p.op.map φ) φ :=
      isStronglyCocartesian_of_isCofiberedInGroupoids
        (p := p.op) hpop (p.op.map φ) φ (Functor.IsHomLift.map φ)
    exact Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (p := p.op) (f := p.op.map φ) φ
  have hz₀arrow : IsIso z₀obj.arrow := isIso_of_op z₀obj.arrow
  let restriction : Aut xε' →* Aut x₀' :=
    pushforwardAutomorphismHom
      (p := p.op) (x' := xε') (x := x₀') hpop
      (p.op.map r.op) r.op (Functor.IsHomLift.map (p := p.op) r.op)
  let F : D.carrier ⥤ Xᵒᵖ := {
    obj := fun a => Opposite.op (D.objects a).point
    map := fun {a b} f => Opposite.op (D.morphisms a b f).arrow
    map_id := by intro a; dsimp; rw [D.reversed_identity]; rfl
    map_comp := by intro a b c f h; dsimp; rw [D.reversed_composition]; rfl
  }
  have ringHom_eq_id (f : zε.1 ⟶ zε.1)
      (hf : D.projection.IsHomLift (𝟙 Aε) f) :
      (D.morphisms zε.1 zε.1 f).ringHom = 𝟙 (D.objects zε.1).algebra := by
    have hmap : D.projection.map f = 𝟙 (D.projection.obj zε.1) := by
      have hf' : D.projection.IsHomLift (𝟙 (D.projection.obj zε.1)) f := by
        rwa [zε.2]
      exact (IsHomLift.eq_of_isHomLift D.projection (𝟙 _) f).symm
    have hproj := D.morphism_projection f
    rw [hmap] at hproj
    simpa using hproj.symm
  have hid : Spec.map (CommRingCat.ofHom
      (𝟙 (D.objects zε.1).algebra :
        (D.objects zε.1).algebra ⟶
          (D.objects zε.1).algebra).hom.toRingHom) =
      𝟙 (Spec (CommRingCat.of (D.objects zε.1).algebra)) := by
    simp [ArtinianLocalAlgCat.id_hom, ← CommRingCat.ofHom_id]
  have qmap_eq_id
      (m : DeformationMorphism iΛ q x₀ hx₀
        (D.objects zε.1) (D.objects zε.1))
      (hm : m.ringHom = 𝟙 (D.objects zε.1).algebra) :
      q.map m.arrow = 𝟙 (q.obj y) := by
    apply Over.OverMorphism.ext
    have hh := m.arrow_base
    rw [hm, hid] at hh
    exact (eqToHom_conj_eq_id_iff _ _).1 hh
  have pmap_eq_id
      (m : DeformationMorphism iΛ q x₀ hx₀
        (D.objects zε.1) (D.objects zε.1))
      (hm : m.ringHom = 𝟙 (D.objects zε.1).algebra) :
      p.map m.arrow = 𝟙 (p.obj y) := by
    have hq : q.map m.arrow = q.map (𝟙 y) := (qmap_eq_id m hm).trans (q.map_id y).symm
    exact (Over.post B.inclusion).map_injective (by simpa [q] using hq)
  have opLift (f : zε.1 ⟶ zε.1)
      (hf : D.projection.IsHomLift (𝟙 Aε) f) :
      p.op.IsHomLift (a := Opposite.op y) (b := Opposite.op y)
        (𝟙 (Opposite.op (p.obj y)))
        (Opposite.op (D.morphisms zε.1 zε.1 f).arrow) := by
    let m := D.morphisms zε.1 zε.1 f
    have hm := ringHom_eq_id f hf
    have hpmap := pmap_eq_id m hm
    apply IsHomLift.of_fac (p := p.op) (a := Opposite.op y) (b := Opposite.op y)
      (f := 𝟙 (Opposite.op (p.obj y))) (φ := Opposite.op m.arrow) rfl rfl
    simpa [Functor.op_map, y] using
      (congrArg Quiver.Hom.op hpmap).symm
  let I := Functor.Fiber.fiberInclusion (p := D.projection) (S := Aε)
  let totalAutMap : Aut zε →* Aut (Opposite.op y) :=
    (Functor.mapAut zε.1 F).comp (Functor.mapAut zε I)
  let toAut (a : Aut zε) : Aut xε' :=
    let b := totalAutMap a
    { hom := ⟨b.hom, opLift (I.map a.hom) a.hom.2⟩
      inv := ⟨b.inv, opLift (I.map a.inv) a.inv.2⟩
      hom_inv_id := Functor.Fiber.hom_ext b.hom_inv_id
      inv_hom_id := Functor.Fiber.hom_ext b.inv_hom_id }
  let toAutHom : Aut zε →* Aut xε' := {
    toFun := toAut
    map_one' := Aut.ext (Functor.Fiber.hom_ext (congrArg Iso.hom totalAutMap.map_one))
    map_mul' a b := Aut.ext (Functor.Fiber.hom_ext (congrArg Iso.hom (totalAutMap.map_mul a b)))
  }
  have toAut_hom (a : Aut zε) :
      (toAutHom a).hom.val.unop =
        (D.morphisms zε.1 zε.1 a.hom.val).arrow := by
    dsimp [toAutHom, toAut, totalAutMap, I, F, Functor.mapAut]
    rfl
  let rc := canonicalRetraction hD g e hpair.split i hi
  let rcMorphism := D.morphisms zε.1 z₀.1 rc.1
  let t := rcMorphism.arrow
  have r_eq : z₀obj.arrow ≫ t = r := rcMorphism.triangle
  have fixed_arrow_iff (f : y ⟶ y) :
      r ≫ f = r ↔ t ≫ f = t := by
    constructor
    · intro hf
      apply (cancel_epi z₀obj.arrow).1
      rw [← r_eq] at hf
      simpa [Category.assoc] using hf
    · intro hf
      rw [← r_eq, Category.assoc, hf]
  have kernel_mem_iff (b : Aut xε') :
      b ∈ MonoidHom.ker restriction ↔ r ≫ b.hom.val.unop = r := by
    show (b ∈ relativeInfinitesimalAutomorphisms
      (p := p.op) (x' := xε') (x := x₀') hpop
      (p.op.map r.op) r.op (Functor.IsHomLift.map (p := p.op) r.op)) ↔ _
    rw [mem_relativeInfinitesimalAutomorphisms_iff]
    constructor
    · intro hf
      simpa [unop_comp] using congrArg Quiver.Hom.unop hf
    · intro hf
      apply Quiver.Hom.unop_inj
      simpa [unop_comp] using hf
  have ringHom_comp (f : zε.1 ⟶ zε.1) :
      (D.morphisms zε.1 z₀.1 (f ≫ rc.1)).ringHom =
        (D.morphisms zε.1 zε.1 f).ringHom ≫ rcMorphism.ringHom := by
    rw [← D.morphism_projection (f ≫ rc.1), ← D.morphism_projection f,
      ← D.morphism_projection rc.1]
    simp [Functor.map_comp, Category.assoc]
  have source_fix_iff (a : Aut zε) :
      a.hom.val ≫ rc.1 = rc.1 ↔
        t ≫ (D.morphisms zε.1 zε.1 a.hom.val).arrow = t := by
    constructor
    · intro hf
      have hm := congrArg (D.morphisms zε.1 z₀.1) hf
      have ha := congrArg (fun m => m.arrow) hm
      rwa [D.reversed_composition] at ha
    · intro hf
      apply (D.morphisms zε.1 z₀.1).injective
      apply DeformationMorphism.ext_of_components
      · rw [ringHom_comp, ringHom_eq_id a.hom.val a.hom.2]
        simp [rcMorphism]
      · calc
          (D.morphisms zε.1 z₀.1 (a.hom.val ≫ rc.1)).arrow =
              t ≫ (D.morphisms zε.1 zε.1 a.hom.val).arrow := by
                rw [D.reversed_composition]
          _ = t := hf
  have source_kernel_iff (a : Aut zε) :
      a ∈ infinitesimalAutomorphisms hD g e hpair i hi ↔
        toAutHom a ∈ MonoidHom.ker restriction := by
    rw [mem_infinitesimalAutomorphisms_iff, kernel_mem_iff]
    simp only [toAut_hom]
    exact (source_fix_iff a).trans (fixed_arrow_iff _).symm
  let sourceGroup := infinitesimalAutomorphisms hD g e hpair i hi
  let targetGroup := MonoidHom.ker restriction
  have kernelToAut (b : targetGroup) :
      {a : Aut zε // (D.morphisms zε.1 zε.1 a.hom.val).arrow =
        b.1.hom.val.unop} := by
    let f : y ⟶ y := b.1.hom.val.unop
    have hfix : r ≫ f = r := (kernel_mem_iff b.1).mp b.2
    have hmap : p.map f = 𝟙 (p.obj y) := by
      let : p.op.IsHomLift (𝟙 (p.op.obj xε'.1)) b.1.hom.val := b.1.hom.2
      have hbase := IsHomLift.eq_of_isHomLift (p := p.op)
        (a := xε'.1) (b := xε'.1) (𝟙 (p.op.obj xε'.1)) b.1.hom.val
      have hunop := congrArg Quiver.Hom.unop hbase
      simpa [f, Functor.op_map] using hunop.symm
    have hq : q.map f = 𝟙 (q.obj y) := by
      show (Over.post B.inclusion).map (p.map f) = _
      rw [hmap]
      exact (Over.post B.inclusion).map_id _
    let m : DeformationMorphism iΛ q x₀ hx₀
        (D.objects zε.1) (D.objects zε.1) := {
      ringHom := 𝟙 (D.objects zε.1).algebra
      arrow := f
      triangle := hfix
      arrow_base := by
        rw [hid]
        exact (eqToHom_conj_eq_id_iff _ _).2 (congrArg Over.Hom.left hq) }
    let fD : zε.1 ⟶ zε.1 := (D.morphisms zε.1 zε.1).symm m
    have hmD : D.morphisms zε.1 zε.1 fD = m := Equiv.apply_symm_apply _ _
    have hmapD : D.projection.map fD = 𝟙 (D.projection.obj zε.1) := by
      have hproj := D.morphism_projection fD
      rw [hmD] at hproj
      exact (eqToHom_conj_eq_id_iff _ _).1 hproj
    have hfLift : D.projection.IsHomLift (𝟙 Aε) fD := by
      apply IsHomLift.of_fac (p := D.projection) (f := 𝟙 Aε) (φ := fD) zε.2 zε.2
      simp [hmapD]
    have hfIso : IsIso fD := isIso_of_isHomLift_id hD fD hfLift
    have hInvLift : D.projection.IsHomLift (𝟙 Aε) (inv fD) :=
      IsHomLift.lift_id_inv_isIso (p := D.projection) Aε fD
    let aIso : zε ≅ zε := {
      hom := ⟨fD, hfLift⟩
      inv := ⟨inv fD, hInvLift⟩
      hom_inv_id := Functor.Fiber.hom_ext (IsIso.hom_inv_id fD)
      inv_hom_id := Functor.Fiber.hom_ext (IsIso.inv_hom_id fD) }
    refine ⟨aIso, ?_⟩
    simp [aIso, fD, m, f]
  let forward : sourceGroup →* targetGroup := {
    toFun := fun a => ⟨toAutHom a.1, (source_kernel_iff a.1).mp a.2⟩
    map_one' := Subtype.ext toAutHom.map_one
    map_mul' a b := Subtype.ext (toAutHom.map_mul a.1 b.1) }
  have forward_injective : Function.Injective forward := by
    intro a b hab
    have hArrow :
        (D.morphisms zε.1 zε.1 a.1.hom.val).arrow =
          (D.morphisms zε.1 zε.1 b.1.hom.val).arrow := by
      have h := congrArg (fun x : targetGroup => x.1.hom.val.unop) hab
      simpa [forward, toAut_hom] using h
    have hringA := ringHom_eq_id a.1.hom.val a.1.hom.2
    have hringB := ringHom_eq_id b.1.hom.val b.1.hom.2
    have hm : D.morphisms zε.1 zε.1 a.1.hom.val = D.morphisms zε.1 zε.1 b.1.hom.val :=
      DeformationMorphism.ext_of_components _ _ _ _ (hringA.trans hringB.symm) hArrow
    exact Subtype.ext (Aut.ext (Subtype.ext ((D.morphisms zε.1 zε.1).injective hm)))
  have forward_surjective : Function.Surjective forward := by
    intro b
    let a := (kernelToAut b).1
    have hto : toAutHom a = b.1 := by
      apply Aut.ext
      apply Subtype.ext
      apply Quiver.Hom.unop_inj
      exact (toAut_hom a).trans (kernelToAut b).2
    have ha : a ∈ sourceGroup := (source_kernel_iff a).2 (by rw [hto]; exact b.2)
    exact ⟨⟨a, ha⟩, Subtype.ext hto⟩
  let E : sourceGroup ≃* targetGroup := MulEquiv.ofBijective forward
    ⟨forward_injective, forward_surjective⟩
  refine ⟨E, ?_, ?_⟩
  · intro a
    show (toAutHom a).hom.val.unop = _
    exact toAut_hom a
  · intro E' hE'
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    apply Aut.ext
    apply Functor.Fiber.hom_ext
    apply Quiver.Hom.unop_inj
    exact (hE' a).trans (toAut_hom a).symm

/-- **Infinitesimal automorphisms of `𝓕_{𝓧,k,x₀}`.** Let `𝓧` be fibred in groupoids over the
big fppf site of `S` and let `x₀` lie over `Spec k`. For a pushforward `z₀ ⟶ zε` of a point of
the special fibre along the constant inclusion `k ⟶ k[ε]`, the infinitesimal automorphisms of
the predeformation category `𝓕_{𝓧,k,x₀}` are canonically the kernel of the restriction
homomorphism from the automorphisms of the dual-number object `x₀'` of `𝓧` to the
automorphisms of `x₀`; the identification keeps the underlying arrow of `𝓧`. -/
@[stacks 07X0]
public theorem infinitesimalAutomorphisms_equiv_restrictionKernel
    (B : BigFppfSite.{u})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (contains : B.Contains S) (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S contains)
    (fibered : p.IsFiberedInGroupoids) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
    letI : Category.{max u w} D.carrier := D.category
    ∀ {A₀ Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
      {z₀ : D.projection.Fiber A₀} {zε : D.projection.Fiber Aε}
      (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
      (hpair : IsCanonicalDualNumberPair g e)
      (i : z₀.1 ⟶ zε.1) (hi : D.projection.IsHomLift g i),
      let y := (D.objects zε.1).point
      let xε' : p.op.Fiber (Opposite.op (p.obj y)) := ⟨Opposite.op y, rfl⟩
      let x₀' : p.op.Fiber (Opposite.op (p.obj x₀)) := ⟨Opposite.op x₀, rfl⟩
      let r := (D.objects zε.1).arrow
      let restriction : Aut xε' →* Aut x₀' :=
        pushforwardAutomorphismHom
          (p := p.op) (x' := xε') (x := x₀')
          (isCofiberedInGroupoids_op_of_isFiberedInGroupoids fibered)
          (p.op.map r.op) r.op (Functor.IsHomLift.map (p := p.op) r.op)
      ∃! E : ↥(infinitesimalAutomorphisms
          (predeformationCategory_isPredeformationCategory B contains iΛ p x₀ hx₀
            fibered).cofibered g e hpair i hi) ≃* ↥(MonoidHom.ker restriction),
        ∀ a, (E a).val.hom.val.unop =
          (D.morphisms zε.1 zε.1 a.val.hom.val).arrow := by
  intro D
  let : Category.{max u w} D.carrier := D.category
  have hD : IsCofiberedInGroupoids D.projection :=
    (predeformationCategory_isPredeformationCategory B contains iΛ p x₀ hx₀ fibered).cofibered
  intro A₀ Aε z₀ zε
  exact infinitesimalAutomorphisms_equiv_restrictionKernel_of_construction B contains iΛ p
    (isCofiberedInGroupoids_op_of_isFiberedInGroupoids fibered) x₀ hx₀ D hD

end Deformation.Artin
