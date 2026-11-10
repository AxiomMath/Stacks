module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableDiagonal.SchemeAndRepresentableSources
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# The groupoid of a chart of a category fibred in groupoids

Let `T'` be an affine object of the big fppf site over `S`, `A' = Γ(T', ⊤)`, let `𝒳` be a
category fibred in groupoids over the site, and let `a : (Sch/U₀) ⟶ 𝒳` be a 1-morphism from the
category represented by an object `U₀` (for instance a presentation of an algebraic stack). A
`κ`-small `A'`-algebra `P` together with a morphism `ι : Spec P ⟶ U₀` of the site gives, for every
small `A'`-algebra `C` and every point `u : P → C`, the object `ξ u = a(ι ∘ Spec u)` of `𝒳` over
`Spec C`.

The *groupoid of the chart* (`AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid`) has as arrows
over `C` the triples `(u₁, u₂, φ)` with `φ : ξ u₁ ⟶ ξ u₂` a morphism of `𝒳` over the identity of
`Spec C`. Its functoriality in `C` is the unique factorisation through the cartesian arrows
`ξ (h ∘ u) ⟶ ξ u` that `a` produces over `Spec h`; this is what makes it a strict functor, with
no choice of pullbacks involved.

This is the groupoid `AlgebraicGeometry.Stack.GroupoidLift.Groupoid` that the first-order lifting
engine `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_lift_arrow` takes, in the case of
a category fibred in groupoids rather than a sheaf of sets
(`AlgebraicGeometry.Stack.GroupoidLift.chartGroupoid`).

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.ξ`: the object of a point.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.Arr`: the arrows.
* `AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid`: the groupoid.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

namespace StackChart

/-- The point `ι ∘ Spec u` of `U₀` over `Spec C`. -/
noncomputable abbrev pt {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) : Over U₀ :=
  Over.mk (specOverMap (SmallAlg.homMk u) ≫ ι)

/-- The object `a(ι ∘ Spec u)` of `𝒳` over `Spec C`. -/
noncomputable abbrev ξ {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) : 𝒳.val.obj :=
  (CatFiberedInGroupoids.homFunctor a).obj (pt ι u)

/-- Composing the point `ι ∘ Spec u` with `Spec h` gives the point `ι ∘ Spec (h ∘ u)`. -/
theorem specOverMap_comp_pt {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    specOverMap h ≫ (pt ι u).hom = (pt ι (h.hom.hom.comp u)).hom := by
  change specOverMap h ≫ specOverMap (SmallAlg.homMk u) ≫ ι =
    specOverMap (SmallAlg.homMk u ≫ h) ≫ ι
  rw [specOverMap_comp, Category.assoc]

/-- The arrow `ξ (h ∘ u) ⟶ ξ u` over `Spec h`. -/
noncomputable def trans {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) : ξ a ι (h.hom.hom.comp u) ⟶ ξ a ι u :=
  (CatFiberedInGroupoids.homFunctor a).map
    (Over.homMk (specOverMap h) (specOverMap_comp_pt ι h u) :
      pt ι (h.hom.hom.comp u) ⟶ pt ι u)

/-- The arrow `trans a ι h u` lies over `Spec h`. -/
instance trans_isHomLift {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    𝒳.val.p.IsHomLift (specOverMap h) (trans a ι h u) := by
  have : (schemeFibredCategory B S hS U₀).val.p.IsHomLift (specOverMap h)
      (Over.homMk (specOverMap h) (specOverMap_comp_pt ι h u) :
        pt ι (h.hom.hom.comp u) ⟶ pt ι u) :=
    show (Over.forget U₀).IsHomLift ((Over.forget U₀).map
      (Over.homMk (specOverMap h) (specOverMap_comp_pt ι h u) :
        pt ι (h.hom.hom.comp u) ⟶ pt ι u)) _ from IsHomLift.map (Over.forget U₀) _
  exact BasedFunctor.preserves_isHomLift a.hom (specOverMap h) _

/-- The arrow `trans a ι h u` is strongly cartesian over `Spec h`. -/
instance trans_isStronglyCartesian {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    𝒳.val.p.IsStronglyCartesian (specOverMap h) (trans a ι h u) :=
  𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift _ _

/-- The arrow over `Spec` of the identity is the identity. -/
theorem trans_id {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) : trans a ι (𝟙 C) u = 𝟙 _ :=
  (congrArg (CatFiberedInGroupoids.homFunctor a).map
    (Over.OverMorphism.ext (specOverMap_id C))).trans
    ((CatFiberedInGroupoids.homFunctor a).map_id _)

/-- The arrow over `Spec (g ∘ h)` is the composite of the arrows over `Spec g` and `Spec h`. -/
theorem trans_comp {C D E : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D) (g : D ⟶ E)
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    trans a ι (h ≫ g) u = trans a ι g (h.hom.hom.comp u) ≫ trans a ι h u :=
  (congrArg (CatFiberedInGroupoids.homFunctor a).map
    (Over.OverMorphism.ext (specOverMap_comp h g))).trans
    ((CatFiberedInGroupoids.homFunctor a).map_comp _ _)

/-- The object `ξ u` lies over `Spec C`. -/
theorem ξ_obj {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (u : P.obj →ₐ[ringOf B S hS T'] C.obj) : 𝒳.val.p.obj (ξ a ι u) = specOver C :=
  BasedFunctor.w_obj a.hom (pt ι u)

/-- **An arrow of the groupoid of a chart** over `C`: two points of `P` and a morphism of `𝒳`
over the identity of `Spec C` between their objects. -/
structure Arr (C : SmallAlg (ringOf B S hS T') B.cutoff) where
  /-- The source. -/
  src : P.obj →ₐ[ringOf B S hS T'] C.obj
  /-- The target. -/
  tgt : P.obj →ₐ[ringOf B S hS T'] C.obj
  /-- The morphism of `𝒳`. -/
  hom : ξ a ι src ⟶ ξ a ι tgt
  /-- It lies over the identity of `Spec C`. -/
  lift : 𝒳.val.p.IsHomLift (𝟙 (specOver C)) hom

attribute [instance] Arr.lift

variable {a ι}

/-- Two arrows with equal endpoints and heterogeneously equal morphisms are equal. -/
theorem Arr.ext_heq {C : SmallAlg (ringOf B S hS T') B.cutoff} {g g' : Arr a ι C}
    (h₁ : g.src = g'.src) (h₂ : g.tgt = g'.tgt) (h : HEq g.hom g'.hom) : g = g' := by
  obtain ⟨s, t, φ, _⟩ := g
  obtain ⟨s', t', φ', _⟩ := g'
  dsimp only at h₁ h₂ h
  subst h₁ h₂
  cases h
  rfl

/-- The morphism of an arrow is an isomorphism. -/
instance Arr.isIso_hom {C : SmallAlg (ringOf B S hS T') B.cutoff} (g : Arr a ι C) :
    IsIso g.hom :=
  haveI := g.lift
  haveI := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 (specOver C)) g.hom
  Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 (specOver C)) g.hom

variable (a ι) in
/-- **The restriction of an arrow along `h : C ⟶ D`**: the unique morphism over the identity
of `Spec D` through which the restricted morphism factors along the cartesian arrows. -/
noncomputable def Arr.map {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (g : Arr a ι C) : Arr a ι D where
  src := h.hom.hom.comp g.src
  tgt := h.hom.hom.comp g.tgt
  hom :=
    haveI := g.lift
    haveI := trans_isStronglyCartesian a ι h g.tgt
    Functor.IsCartesian.map 𝒳.val.p (specOverMap h) (trans a ι h g.tgt)
      (trans a ι h g.src ≫ g.hom)
  lift :=
    haveI := g.lift
    haveI := trans_isStronglyCartesian a ι h g.tgt
    Functor.IsCartesian.map_isHomLift 𝒳.val.p (specOverMap h) (trans a ι h g.tgt) _

/-- The morphism of the restriction of `g` along `h`, followed by the cartesian arrow over
`Spec h` at the target, equals the cartesian arrow at the source followed by `g.hom`. -/
theorem Arr.map_hom_fac {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (g : Arr a ι C) :
    (Arr.map a ι h g).hom ≫ trans a ι h g.tgt = trans a ι h g.src ≫ g.hom :=
  have := g.lift
  have := trans_isStronglyCartesian a ι h g.tgt
  Functor.IsCartesian.fac 𝒳.val.p (specOverMap h) (trans a ι h g.tgt)
    (trans a ι h g.src ≫ g.hom)

/-- **The characterisation of the restriction**: an arrow over `D` with the restricted
endpoints whose morphism satisfies the factorisation is the restriction. -/
theorem Arr.map_eq_mk {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (g : Arr a ι C) (ψ : ξ a ι (h.hom.hom.comp g.src) ⟶ ξ a ι (h.hom.hom.comp g.tgt))
    (hl : 𝒳.val.p.IsHomLift (𝟙 (specOver D)) ψ)
    (hψ : ψ ≫ trans a ι h g.tgt = trans a ι h g.src ≫ g.hom) :
    Arr.map a ι h g = ⟨h.hom.hom.comp g.src, h.hom.hom.comp g.tgt, ψ, hl⟩ := by
  refine Arr.ext_heq rfl rfl (heq_of_eq ?_)
  have := g.lift
  have := trans_isStronglyCartesian a ι h g.tgt
  exact (Functor.IsCartesian.map_uniq 𝒳.val.p (specOverMap h) (trans a ι h g.tgt)
    (trans a ι h g.src ≫ g.hom) ψ hψ).symm

/-- Restriction along the identity is the identity. -/
theorem Arr.map_id {C : SmallAlg (ringOf B S hS T') B.cutoff} (g : Arr a ι C) :
    Arr.map a ι (𝟙 C) g = g :=
  Arr.map_eq_mk (𝟙 C) g g.hom g.lift (by
    rw [trans_id, trans_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Restriction along `h ≫ k` is restriction along `h` followed by restriction along `k`. -/
theorem Arr.map_comp {C D E : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D) (k : D ⟶ E)
    (g : Arr a ι C) : Arr.map a ι (h ≫ k) g = Arr.map a ι k (Arr.map a ι h g) := by
  have h₁ : (Arr.map a ι k (Arr.map a ι h g)).hom ≫ trans a ι k (h.hom.hom.comp g.tgt) =
      trans a ι k (h.hom.hom.comp g.src) ≫ (Arr.map a ι h g).hom :=
    Arr.map_hom_fac k (Arr.map a ι h g)
  have h₂ := Arr.map_hom_fac h g
  exact Arr.map_eq_mk (h ≫ k) g (Arr.map a ι k (Arr.map a ι h g)).hom
    (Arr.map a ι k (Arr.map a ι h g)).lift (by
      rw [trans_comp, trans_comp]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ trans a ι h g.tgt) h₁).trans
        ((Category.assoc _ _ _).trans ((congrArg (trans a ι k (h.hom.hom.comp g.src) ≫ ·) h₂).trans
          (Category.assoc _ _ _).symm))))

/-- The composite of two arrows. -/
noncomputable def Arr.comp {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (g f : Arr a ι C) (hgf : g.src = f.tgt) : Arr a ι C where
  src := f.src
  tgt := g.tgt
  hom := f.hom ≫ eqToHom (congrArg (ξ a ι) hgf.symm) ≫ g.hom
  lift :=
    haveI := f.lift
    haveI := g.lift
    inferInstance

/-- The inverse of an arrow. -/
noncomputable def Arr.inv {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (g : Arr a ι C) : Arr a ι C where
  src := g.tgt
  tgt := g.src
  hom := CategoryTheory.inv g.hom
  lift :=
    haveI := g.lift
    inferInstance

/-- The identity arrow of a point. -/
noncomputable def Arr.idt {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (w : P.obj →ₐ[ringOf B S hS T'] C.obj) : Arr a ι C where
  src := w
  tgt := w
  hom := 𝟙 _
  lift := IsHomLift.id (ξ_obj a ι w)

/-- Restriction commutes with the composite of arrows. -/
theorem Arr.map_comp_arr {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (g f : Arr a ι C) (hgf : g.src = f.tgt) (hgf' : (Arr.map a ι h g).src = (Arr.map a ι h f).tgt) :
    Arr.map a ι h (g.comp f hgf) = (Arr.map a ι h g).comp (Arr.map a ι h f) hgf' := by
  obtain ⟨gs, gt, gφ, gl⟩ := g
  obtain ⟨fs, ft, fφ, fl⟩ := f
  dsimp only at hgf
  subst hgf
  have h₁ := Arr.map_hom_fac h ⟨fs, gs, fφ, fl⟩
  have h₂ := Arr.map_hom_fac h ⟨gs, gt, gφ, gl⟩
  dsimp only at h₁ h₂
  refine Arr.map_eq_mk h _ _ _ ?_
  have e₁ : (Arr.map a ι h ⟨fs, gs, fφ, fl⟩).hom ≫ 𝟙 _ ≫ (Arr.map a ι h ⟨gs, gt, gφ, gl⟩).hom =
      (Arr.map a ι h ⟨fs, gs, fφ, fl⟩).hom ≫ (Arr.map a ι h ⟨gs, gt, gφ, gl⟩).hom :=
    congrArg ((Arr.map a ι h ⟨fs, gs, fφ, fl⟩).hom ≫ ·) (Category.id_comp _)
  have e₂ : trans a ι h fs ≫ fφ ≫ 𝟙 _ ≫ gφ = trans a ι h fs ≫ fφ ≫ gφ :=
    congrArg (fun t ↦ trans a ι h fs ≫ fφ ≫ t) (Category.id_comp _)
  refine (congrArg (· ≫ trans a ι h gt) e₁).trans (Eq.trans ?_ e₂.symm)
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg ((Arr.map a ι h ⟨fs, gs, fφ, fl⟩).hom ≫ ·) h₂).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ gφ) h₁).trans (Category.assoc _ _ _)))

/-- Restriction commutes with the inverse of an arrow. -/
theorem Arr.map_inv {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (g : Arr a ι C) : Arr.map a ι h g.inv = (Arr.map a ι h g).inv := by
  refine Arr.map_eq_mk h _ _ _ ?_
  have h₁ := Arr.map_hom_fac h g
  change CategoryTheory.inv (Arr.map a ι h g).hom ≫ trans a ι h g.src =
    trans a ι h g.tgt ≫ CategoryTheory.inv g.hom
  refine (IsIso.inv_comp_eq _).2 ?_
  have e : trans a ι h g.src = trans a ι h g.src ≫ g.hom ≫ CategoryTheory.inv g.hom := by
    rw [IsIso.hom_inv_id, Category.comp_id]
  exact e.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ CategoryTheory.inv g.hom) h₁.symm).trans (Category.assoc _ _ _)))

/-- The restriction of the identity arrow of `w` is the identity arrow of `h ∘ w`. -/
theorem Arr.map_idt {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (w : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    Arr.map a ι h (Arr.idt w) = Arr.idt (h.hom.hom.comp w) := by
  refine Arr.map_eq_mk h _ _ _ ?_
  change 𝟙 _ ≫ trans a ι h w = trans a ι h w ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

end StackChart

open StackChart

/-- The presheaf of arrows of the groupoid of a chart. -/
noncomputable def stackArr : SmallAlg (ringOf B S hS T') B.cutoff ⥤ Type u where
  obj C := Arr a ι C
  map h := TypeCat.ofHom (Arr.map a ι h)
  map_id C := by
    ext g
    exact Arr.map_id g
  map_comp h k := by
    ext g
    exact Arr.map_comp h k g

/-- The action of `stackArr` on a morphism `h` is restriction along `h`. -/
theorem stackArr_map {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (g : Arr a ι C) : (stackArr a ι).map h g = Arr.map a ι h g := rfl

/-- **The groupoid of a chart** of a category fibred in groupoids: arrows over `C` are the
morphisms of `𝒳` over the identity of `Spec C` between the objects of two points of `P`. -/
noncomputable def stackGroupoid : Groupoid (ringOf B S hS T') B.cutoff P.obj where
  arr := stackArr a ι
  src g := Arr.src (a := a) (ι := ι) g
  tgt g := Arr.tgt (a := a) (ι := ι) g
  idt w := Arr.idt w
  comp g f h := Arr.comp (a := a) (ι := ι) g f h
  inv g := Arr.inv (a := a) (ι := ι) g
  src_map _ _ := rfl
  tgt_map _ _ := rfl
  idt_map h w := Arr.map_idt h w
  comp_map h g f hgf := Arr.map_comp_arr h g f hgf _
  inv_map h g := Arr.map_inv h g
  src_idt _ := rfl
  tgt_idt _ := rfl
  src_comp _ _ _ := rfl
  tgt_comp _ _ _ := rfl
  src_inv _ := rfl
  tgt_inv _ := rfl
  comp_idt g := Arr.ext_heq rfl rfl (heq_of_eq (by simp [Arr.comp, Arr.idt]))
  idt_comp g := Arr.ext_heq rfl rfl (heq_of_eq (by simp [Arr.comp, Arr.idt]))
  comp_inv g := Arr.ext_heq rfl rfl (heq_of_eq (by simp [Arr.comp, Arr.inv, Arr.idt]))
  inv_comp g := Arr.ext_heq rfl rfl (heq_of_eq (by simp [Arr.comp, Arr.inv, Arr.idt]))
  assoc h g f hhg hgf := Arr.ext_heq rfl rfl (heq_of_eq (by simp [Arr.comp]))

end AlgebraicGeometry.Stack.GroupoidLift

end
