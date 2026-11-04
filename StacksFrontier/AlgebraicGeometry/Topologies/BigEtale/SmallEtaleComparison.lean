module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.CompatibleSystem

/-!
# Sheaves on the big étale site from sheaves on the small étale sites

Let `B` be a big étale site containing a scheme `S`. Restricting a sheaf on the big étale site
over `S` to the small étale site of each scheme `T` over `S` produces a compatible system of
small étale sheaves in the sense of `AlgebraicGeometry.BigEtaleSheafData`. This file proves
that this restriction functor is an equivalence: a sheaf on the big étale site over `S` *is*
such a compatible system.

The inverse construction evaluates the system at the final object of each small étale site:
the presheaf `T ↦ 𝓕_T(T)` on the big étale category over `S`. Its restriction to the small
étale site of `T` is identified with `𝓕_T` because the comparison map along an étale morphism
is an isomorphism, which is where that hypothesis on the data is used; the sheaf condition for
the big site then follows from the sheaf condition for the small sites, since every covering
family of the big site is, after base change, a covering family by étale objects.

## Main definitions

* `AlgebraicGeometry.bigEtaleSheafRestriction` — the canonical functor from sheaves on the big
  étale site over `S` to compatible systems, given by restriction to each small étale site.

## Main results

* `AlgebraicGeometry.characterizeSheafBigEtale` — the equivalence between sheaves on the big
  étale site over `S` and compatible systems of small étale sheaves.
* `AlgebraicGeometry.characterizeSheafBigEtale_functor_comp_eval` — the equivalence is
  restriction: evaluating it at `T` is restriction to the small étale site of `T`.
* `AlgebraicGeometry.characterizeSheafBigEtale_pullback_app` — under that identification the
  adjoint of each comparison map is restriction along the projection `U ×[T] T' ⟶ U`, so the
  equivalence also determines the comparison maps.
* `AlgebraicGeometry.bigEtaleSheafRestriction_isEquivalence` — the restriction functor itself,
  rather than merely some functor, is the equivalence.

## Implementation notes

Two descriptions of the sections of a reconstructed sheaf are used throughout. The first,
`reconstructedPresheafMap`, is the one that makes the functoriality on the big site evident:
sections over `T` are sections of `𝓕_T` over the final object of the small étale site of `T`,
and a morphism acts by the adjoint comparison map followed by the canonical identification of
final objects. The second, `sectionMap`, is indexed by an arbitrary morphism of schemes over
the base and composes strictly; the two agree, and it is the second that makes the cocycle
bookkeeping routine.

## References

* [Stacks Project, Tag 021K](https://stacks.math.columbia.edu/tag/021K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- The reconstruction moves constantly between the sections of a small étale sheaf over a
-- base-changed object and the sections of its direct image over the original object, and
-- between the final object of a small étale site and the scheme it lies over.  Each identity
-- holds by definition, and recognizing it is instance-level unfolding of the site functors.
attribute [local implicit_reducible] smallEtaleBaseChange SmallEtale.final
  CategoryTheory.Functor.sheafPushforwardContinuous bigEtaleSheafRestrictionAt

/-- The adjoint of a comparison map of a compatible system, as a morphism into a direct
image. -/
public def dataPushforwardMap (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    D.sheaf T ⟶ (B.smallPushforward f.left (Type (max (u + 1) v))).obj (D.sheaf T') :=
  (B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _ (D.pullback f)

public theorem dataPushforwardMap_app (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
    (U : SmallEtale B T.left.1 T.left.property) :
    (dataPushforwardMap B S hS D f).hom.app (op U) =
      ((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).unit.app
        (D.sheaf T)).hom.app (op U) ≫
          (D.pullback f).hom.app (op ((smallEtaleBaseChange B f.left).obj U)) := by
  dsimp [dataPushforwardMap]
  rw [Adjunction.homEquiv_apply]
  rfl

public theorem dataPushforwardMap_hom_naturality
    {D E : BigEtaleSheafData.{u, v} B S hS}
    (φ : BigEtaleSheafData.Hom B S hS D E)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    φ.app T ≫ dataPushforwardMap B S hS E f =
      dataPushforwardMap B S hS D f ≫
        (B.smallPushforward f.left (Type (max (u + 1) v))).map (φ.app T') :=
  (B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv_naturality_left_square
    (φ.app T) (E.pullback f) (D.pullback f) (φ.app T') (φ.naturality f)

/-- The final object of the small étale site of a scheme over `S`. -/
public abbrev smallEtaleTerminal (T : BigEtaleOver B S hS) :
    SmallEtale B T.left.1 T.left.property :=
  SmallEtale.final B T.left.1 T.left.property

/-- Base change preserves the final object of a small étale site, so it identifies the two. -/
public def smallEtaleBaseChangeTerminalIso
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    (smallEtaleBaseChange B f.left).obj (smallEtaleTerminal B S hS T) ≅
      smallEtaleTerminal B S hS T' :=
  (SmallEtale.finalIsTerminal B T.left.1 T.left.property).isTerminalObj
    (smallEtaleBaseChange B f.left) |>.uniqueUpToIso
      (SmallEtale.finalIsTerminal B T'.left.1 T'.left.property)

/-- The comparison of successive direct images with the direct image along a composite, at the
value universe used here. -/
public abbrev smallPushforwardCompIso {T T' T'' : BigEtaleOver B S hS}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    B.smallPushforward g.left (Type (max (u + 1) v)) ⋙
        B.smallPushforward f.left (Type (max (u + 1) v)) ≅
      B.smallPushforward (g ≫ f).left (Type (max (u + 1) v)) :=
  smallEtaleSheafPushforwardCompIso B T''.left T'.left T.left g.left f.left
    (Type (max (u + 1) v))

/-- On sections, the comparison of successive direct images is restriction along the comparison
of the underlying site functors. -/
public theorem smallPushforwardCompIso_hom_app_app
    {T T' T'' : BigEtaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (X : Sheaf (SmallEtale.topology B T''.left.1 T''.left.property) (Type (max (u + 1) v)))
    (U : SmallEtale B T.left.1 T.left.property) :
    ((smallPushforwardCompIso B S hS f g).hom.app X).hom.app (op U) =
      X.obj.map ((smallEtaleBaseChange_compIso B T''.left T'.left T.left
        g.left f.left).val.inv.app U).op := rfl

/-- The comparison of successive inverse images with the inverse image along a composite, at the
value universe used here. -/
public abbrev smallInverseImageCompIso {T T' T'' : BigEtaleOver B S hS}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    B.smallInverseImage f.left (Type (max (u + 1) v)) ⋙
        B.smallInverseImage g.left (Type (max (u + 1) v)) ≅
      B.smallInverseImage (g ≫ f).left (Type (max (u + 1) v)) :=
  smallEtaleSheafPullbackCompIso B T''.left T'.left T.left g.left f.left
    (Type (max (u + 1) v))

public theorem smallEtaleBaseChangeTerminalIso_comp
    {T T' T'' : BigEtaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    Functor.mapIso (smallEtaleBaseChange B g.left)
        (smallEtaleBaseChangeTerminalIso B S hS f) ≪≫
      smallEtaleBaseChangeTerminalIso B S hS g =
    (smallEtaleBaseChange_compIso B T''.left T'.left T.left
      g.left f.left).val.app (smallEtaleTerminal B S hS T) ≪≫
      smallEtaleBaseChangeTerminalIso B S hS (g ≫ f) := by
  apply Iso.ext
  apply (SmallEtale.finalIsTerminal B T''.left.1 T''.left.property).hom_ext

/-- The comparison of successive inverse images is the uniqueness isomorphism of the left adjoints
of the composite of the adjunctions and of the adjunction along the composite. -/
private theorem smallInverseImageCompIso_eq_leftAdjointUniq
    {T T' T'' : BigEtaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    smallInverseImageCompIso B S hS f g =
      Adjunction.leftAdjointUniq
        (((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).comp
          (B.smallPullbackAdjunction g.left (Type (max (u + 1) v)))).ofNatIsoRight
            (smallPushforwardCompIso B S hS f g))
        (B.smallPullbackAdjunction (g ≫ f).left (Type (max (u + 1) v))) := by
  apply Iso.ext
  apply (conjugateEquiv (B.smallPullbackAdjunction (g ≫ f).left (Type (max (u + 1) v)))
    ((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).comp
      (B.smallPullbackAdjunction g.left (Type (max (u + 1) v))))).injective
  rw [Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom]
  exact Equiv.apply_symm_apply _ (smallPushforwardCompIso B S hS f g).inv

public theorem dataPushforwardMap_comp (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' T'' : BigEtaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    dataPushforwardMap B S hS D f ≫
      (B.smallPushforward f.left (Type (max (u + 1) v))).map
          (dataPushforwardMap B S hS D g) ≫
        (smallPushforwardCompIso B S hS f g).hom.app (D.sheaf T'') =
      dataPushforwardMap B S hS D (g ≫ f) := by
  let adj₁ := B.smallPullbackAdjunction f.left (Type (max (u + 1) v))
  let adj₂ := B.smallPullbackAdjunction g.left (Type (max (u + 1) v))
  let adj₃ := B.smallPullbackAdjunction (g ≫ f).left (Type (max (u + 1) v))
  let e := smallPushforwardCompIso B S hS f g
  let adj := (adj₁.comp adj₂).ofNatIsoRight e
  have hL : adj.homEquiv (D.sheaf T) (D.sheaf T'')
      ((B.smallInverseImage g.left (Type (max (u + 1) v))).map (D.pullback f) ≫
        D.pullback g) =
    dataPushforwardMap B S hS D f ≫
      (B.smallPushforward f.left (Type (max (u + 1) v))).map
          (dataPushforwardMap B S hS D g) ≫
        e.hom.app (D.sheaf T'') := by
    dsimp only [adj]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv, Equiv.trans_apply,
      adj₂.homEquiv_naturality_left, adj₁.homEquiv_naturality_right]
    rfl
  calc
    _ = adj.homEquiv (D.sheaf T) (D.sheaf T'')
        ((B.smallInverseImage g.left (Type (max (u + 1) v))).map (D.pullback f) ≫
          D.pullback g) := hL.symm
    _ = adj.homEquiv (D.sheaf T) (D.sheaf T'')
        ((smallInverseImageCompIso B S hS f g).hom.app (D.sheaf T) ≫
          D.pullback (g ≫ f)) := congrArg
            (fun q => adj.homEquiv (D.sheaf T) (D.sheaf T'') q) (D.pullback_comp f g)
    _ = dataPushforwardMap B S hS D (g ≫ f) := by
      rw [smallInverseImageCompIso_eq_leftAdjointUniq]
      exact Adjunction.homEquiv_leftAdjointUniq_hom_app_comp adj adj₃ (D.pullback (g ≫ f))

/-- The action on sections of the presheaf reconstructed from a compatible system: sections
over `T` are the sections of the sheaf at `T` over the final object of its small étale site. -/
public def reconstructedPresheafMap (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    (D.sheaf T).1.obj (op (smallEtaleTerminal B S hS T)) ⟶
      (D.sheaf T').1.obj (op (smallEtaleTerminal B S hS T')) :=
  (dataPushforwardMap B S hS D f).hom.app
      (op (smallEtaleTerminal B S hS T)) ≫
    (D.sheaf T').1.map (smallEtaleBaseChangeTerminalIso B S hS f).inv.op

/-- Pasting the three squares that express a composite of two restriction-adjoint maps. -/
private theorem comp_eq_of_comm_squares {𝒞 : Type*} [Category 𝒞] {a b b' c c' d e : 𝒞}
    {qf : a ⟶ b} {qg : b ⟶ c} {mδ : c ⟶ d} {qgf : a ⟶ d} {mf : b ⟶ b'} {qg' : b' ⟶ c'}
    {mgf : c ⟶ c'} {mg : c' ⟶ e} {m : d ⟶ e}
    (hc : qf ≫ qg ≫ mδ = qgf) (hn : mf ≫ qg' = qg ≫ mgf) (hm : mgf ≫ mg = mδ ≫ m) :
    (qf ≫ mf) ≫ qg' ≫ mg = qgf ≫ m := by
  subst hc
  simp only [Category.assoc]
  rw [reassoc_of% hn, hm]

public theorem reconstructedPresheafMap_comp (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' T'' : BigEtaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    reconstructedPresheafMap B S hS D (g ≫ f) =
      reconstructedPresheafMap B S hS D f ≫ reconstructedPresheafMap B S hS D g := by
  let A := smallEtaleTerminal B S hS T
  let cf := smallEtaleBaseChangeTerminalIso B S hS f
  let cg := smallEtaleBaseChangeTerminalIso B S hS g
  let cgf := smallEtaleBaseChangeTerminalIso B S hS (g ≫ f)
  let comp := smallEtaleBaseChange_compIso B T''.left T'.left T.left g.left f.left
  have hc := congrArg (fun q => q.hom.app (op A))
    (dataPushforwardMap_comp B S hS D f g)
  have hn := (dataPushforwardMap B S hS D g).hom.naturality cf.inv.op
  have hterm := smallEtaleBaseChangeTerminalIso_comp B S hS f g
  let qf : (D.sheaf T).1.obj (op A) ⟶
      (D.sheaf T').1.obj (op ((smallEtaleBaseChange B f.left).obj A)) :=
    (dataPushforwardMap B S hS D f).hom.app (op A)
  let qg : (D.sheaf T').1.obj (op ((smallEtaleBaseChange B f.left).obj A)) ⟶
      (D.sheaf T'').1.obj (op ((smallEtaleBaseChange B g.left).obj
        ((smallEtaleBaseChange B f.left).obj A))) :=
    (dataPushforwardMap B S hS D g).hom.app
      (op ((smallEtaleBaseChange B f.left).obj A))
  let qgA : (D.sheaf T').1.obj (op (smallEtaleTerminal B S hS T')) ⟶
      (D.sheaf T'').1.obj (op ((smallEtaleBaseChange B g.left).obj
        (smallEtaleTerminal B S hS T'))) :=
    (dataPushforwardMap B S hS D g).hom.app
      (op (smallEtaleTerminal B S hS T'))
  let mcf := (D.sheaf T').1.map cf.inv.op
  let mcg := (D.sheaf T'').1.map cg.inv.op
  let mcgf := (D.sheaf T'').1.map cgf.inv.op
  let mgcf : (D.sheaf T'').1.obj (op ((smallEtaleBaseChange B g.left).obj
        ((smallEtaleBaseChange B f.left).obj A))) ⟶
      (D.sheaf T'').1.obj (op ((smallEtaleBaseChange B g.left).obj
        (smallEtaleTerminal B S hS T'))) :=
    ((B.smallPushforward g.left (Type (max (u + 1) v))).obj
      (D.sheaf T'')).1.map cf.inv.op
  let mδ := (D.sheaf T'').1.map (comp.val.inv.app A).op
  let qgf : (D.sheaf T).1.obj (op A) ⟶
      (D.sheaf T'').1.obj (op ((smallEtaleBaseChange B (g ≫ f).left).obj A)) :=
    (dataPushforwardMap B S hS D (g ≫ f)).hom.app (op A)
  have hn' : mcf ≫ qgA = qg ≫ mgcf := hn
  have hterm' : cg.inv ≫ (smallEtaleBaseChange B g.left).map cf.inv =
      cgf.inv ≫ comp.val.inv.app A := by
    have hi := congrArg Iso.inv hterm
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] using hi
  have hmap : mgcf ≫ mcg = mδ ≫ mcgf := by
    show (D.sheaf T'').1.map
        ((smallEtaleBaseChange B g.left).map cf.inv).op ≫
        (D.sheaf T'').1.map cg.inv.op =
      (D.sheaf T'').1.map (comp.val.inv.app A).op ≫
        (D.sheaf T'').1.map cgf.inv.op
    rw [← Functor.map_comp, ← op_comp]
    conv_rhs => rw [← Functor.map_comp, ← op_comp]
    exact congrArg (D.sheaf T'').1.map
      (congrArg (fun k => k.op) hterm')
  have hc' : qf ≫ qg ≫ mδ = qgf := hc
  exact (comp_eq_of_comm_squares hc' hn' hmap).symm

/-- Direct image along the identity is the identity functor on small étale sheaves. -/
public def smallPushforwardIdIso (T : B.Scheme) :
    B.smallPushforward (𝟙 T) (Type (max (u + 1) v)) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChange_idIso B T)
    (Type (max (u + 1) v)) (SmallEtale.topology B T.1 T.property)

/-- The components of an isomorphism of sheaves are isomorphisms. -/
private theorem isIso_hom_app_of_isIso {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {X Y : Sheaf J (Type (max (u + 1) v))} (f : X ⟶ Y) [IsIso f]
    (U : Cᵒᵖ) :
    IsIso (f.hom.app U) :=
  inferInstanceAs (IsIso ((sheafToPresheaf J _ ⋙ (evaluation _ _).obj U).map f))

public theorem reconstructedPresheafMap_id
    (D : BigEtaleSheafData.{u, v} B S hS)
    (T : BigEtaleOver B S hS) :
    reconstructedPresheafMap B S hS D (𝟙 T) = 𝟙 _ := by
  let A := smallEtaleTerminal B S hS T
  let p := reconstructedPresheafMap B S hS D (𝟙 T)
  let adj := B.smallPullbackAdjunction (𝟙 T.left) (Type (max (u + 1) v))
  have : (B.smallPushforward (𝟙 T.left) (Type (max (u + 1) v))).IsEquivalence :=
    Functor.isEquivalence_of_iso (smallPushforwardIdIso B T.left).symm
  have : IsIso (adj.unit.app (D.sheaf T)) := inferInstance
  have : Etale (B.inclusion.map (𝟙 T.left)) := by infer_instance
  have : IsIso (D.pullback (𝟙 T)) := D.isIso_pullback (𝟙 T)
  have hu := isIso_hom_app_of_isIso (adj.unit.app (D.sheaf T)) (op A)
  have hpull := isIso_hom_app_of_isIso (D.pullback (𝟙 T))
    (op ((smallEtaleBaseChange B (𝟙 T.left)).obj A))
  have : IsIso ((dataPushforwardMap B S hS D (𝟙 T)).hom.app (op A)) := by
    rw [dataPushforwardMap_app]
    exact IsIso.comp_isIso' hu hpull
  have : IsIso ((D.sheaf T).1.map
      (smallEtaleBaseChangeTerminalIso B S hS (𝟙 T)).inv.op) := inferInstance
  have : IsIso p := by
    dsimp [p, reconstructedPresheafMap]
    exact IsIso.comp_isIso'
      (show IsIso ((dataPushforwardMap B S hS D (𝟙 T)).hom.app (op A)) from inferInstance)
      (show IsIso ((D.sheaf T).1.map
        (smallEtaleBaseChangeTerminalIso B S hS (𝟙 T)).inv.op) from inferInstance)
  have h := reconstructedPresheafMap_comp B S hS D (𝟙 T) (𝟙 T)
  rw [Category.id_comp] at h
  exact (cancel_mono p).mp (h.symm.trans (Category.id_comp p).symm)

public theorem reconstructedPresheafMap_hom_naturality
    {D E : BigEtaleSheafData.{u, v} B S hS}
    (φ : BigEtaleSheafData.Hom B S hS D E)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    (φ.app T).hom.app (op (smallEtaleTerminal B S hS T)) ≫
        reconstructedPresheafMap B S hS E f =
      reconstructedPresheafMap B S hS D f ≫
        (φ.app T').hom.app (op (smallEtaleTerminal B S hS T')) := by
  let A := smallEtaleTerminal B S hS T
  let cf := smallEtaleBaseChangeTerminalIso B S hS f
  let mD := (D.sheaf T').1.map cf.inv.op
  let mE := (E.sheaf T').1.map cf.inv.op
  have hq' : (φ.app T).hom.app (op A) ≫
      (dataPushforwardMap B S hS E f).hom.app (op A) =
      (dataPushforwardMap B S hS D f).hom.app (op A) ≫ (φ.app T').hom.app
        (op ((smallEtaleBaseChange B f.left).obj A)) :=
    congrArg (fun q => q.hom.app (op A)) (dataPushforwardMap_hom_naturality B S hS φ f)
  have hn' : (φ.app T').hom.app
      (op ((smallEtaleBaseChange B f.left).obj A)) ≫ mE =
      mD ≫ (φ.app T').hom.app (op (smallEtaleTerminal B S hS T')) :=
    ((φ.app T').hom.naturality cf.inv.op).symm
  calc
    (φ.app T).hom.app (op A) ≫
        (dataPushforwardMap B S hS E f).hom.app (op A) ≫ mE =
        (dataPushforwardMap B S hS D f).hom.app (op A) ≫
          (φ.app T').hom.app
            (op ((smallEtaleBaseChange B f.left).obj A)) ≫ mE :=
      congrArg (fun k => k ≫ (E.sheaf T').1.map cf.inv.op) hq'
    _ = (dataPushforwardMap B S hS D f).hom.app (op A) ≫ mD ≫
        (φ.app T').hom.app (op (smallEtaleTerminal B S hS T')) :=
      congrArg (fun k => (dataPushforwardMap B S hS D f).hom.app (op A) ≫ k) hn'

/-- The presheaf on the big étale site over `S` reconstructed from a compatible system. -/
public def reconstructedPresheaf (D : BigEtaleSheafData.{u, v} B S hS) :
    (BigEtaleOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v) where
  obj T := (D.sheaf T.unop).1.obj (op (smallEtaleTerminal B S hS T.unop))
  map f := reconstructedPresheafMap B S hS D f.unop
  map_id T := reconstructedPresheafMap_id B S hS D T.unop
  map_comp f g := reconstructedPresheafMap_comp B S hS D f.unop g.unop

public def reconstructedPresheafFunctor : BigEtaleSheafData.{u, v} B S hS ⥤
    (BigEtaleOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v) where
  obj D := reconstructedPresheaf B S hS D
  map φ := {
    app T := (φ.app T.unop).hom.app (op (smallEtaleTerminal B S hS T.unop))
    naturality {T T'} f :=
      (reconstructedPresheafMap_hom_naturality B S hS φ f.unop).symm }
  map_id D := by
    apply NatTrans.ext
    funext T
    rfl
  map_comp φ ψ := by
    apply NatTrans.ext
    funext T
    rfl

/-- The structure morphism of a small étale object of `T`, as a morphism over `S`. -/
public def smallStructureArrow (T : BigEtaleOver B S hS)
    (U : SmallEtale B T.left.1 T.left.property) :
    (smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).obj U ⟶ T :=
  Over.homMk U.obj.hom

/-- The structure morphism of a small étale object is étale, in the form indexed by the
corresponding morphism of the big étale site over `S`. -/
public instance etale_smallStructureArrow (T : BigEtaleOver B S hS)
    (U : SmallEtale B T.left.1 T.left.property) :
    Etale (B.inclusion.map (smallStructureArrow B S hS T U).left) :=
  U.property

/-- Sections of the sheaf at `T` over a small étale object `U` are the sections of the
reconstructed presheaf over `U`, viewed as a scheme over `S`. -/
public def reconstructedSmallSectionsMap
    (D : BigEtaleSheafData.{u, v} B S hS) (T : BigEtaleOver B S hS)
    (U : SmallEtale B T.left.1 T.left.property) :
    (D.sheaf T).1.obj (op U) ⟶
      (reconstructedPresheaf B S hS D).obj
        (op ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).obj U)) :=
  ((smallInverseImageIsoPostcomposePushforward B (smallStructureArrow B S hS T U).left
      (Type (max (u + 1) v))).inv.app (D.sheaf T)).hom.app
    (op (smallEtaleTerminal B S hS
      ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).obj U))) ≫
  (D.pullback (smallStructureArrow B S hS T U)).hom.app
    (op (smallEtaleTerminal B S hS
      ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).obj U)))

public theorem reconstructedSmallSectionsMap_isIso
    (D : BigEtaleSheafData.{u, v} B S hS) (T : BigEtaleOver B S hS)
    (U : SmallEtale B T.left.1 T.left.property) :
    IsIso (reconstructedSmallSectionsMap B S hS D T U) := by
  have : IsIso (D.pullback (smallStructureArrow B S hS T U)) :=
    D.isIso_pullback (smallStructureArrow B S hS T U)
  exact IsIso.comp_isIso' (isIso_hom_app_of_isIso _ _) (isIso_hom_app_of_isIso _ _)

/-- The first projection of the comparison of two successive base changes with base change
along the composite. -/
public theorem smallBaseChangeComp_inv_fst
    {T T' T'' : B.Scheme} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : SmallEtale B T.1 T.property) :
    ((smallEtaleBaseChange_compIso B T'' T' T g f).val.inv.app U).hom.left ≫
        pullback.fst (pullback.snd U.obj.hom f) g ≫ pullback.fst U.obj.hom f =
      pullback.fst U.obj.hom (g ≫ f) := by
  have hh := smallEtaleBaseChange_compIso_app B T'' T' T g f U
  change ((smallEtaleBaseChange_compIso B T'' T' T g f).val.hom.app U).hom =
    (Over.pullbackComp g f).inv.app U.obj at hh
  have hi : ((smallEtaleBaseChange_compIso B T'' T' T g f).val.inv.app U).hom =
      (Over.pullbackComp g f).hom.app U.obj := by
    apply (cancel_mono
      ((smallEtaleBaseChange_compIso B T'' T' T g f).val.hom.app U).hom).mp
    conv_rhs => rw [hh]
    show (SmallEtale.inclusion B T''.1 T''.property).map
      ((smallEtaleBaseChange_compIso B T'' T' T g f).val.inv.app U ≫
        (smallEtaleBaseChange_compIso B T'' T' T g f).val.hom.app U) = _
    simp
  rw [hi]
  have hc : (Over.map g ⋙ Over.map f).map ((Over.pullbackComp g f).hom.app U.obj) ≫
        ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f)).counit.app U.obj =
      (Over.mapComp g f).inv.app ((Over.pullback (g ≫ f)).obj U.obj) ≫
        (Over.mapPullbackAdj (g ≫ f)).counit.app U.obj :=
    conjugateEquiv_counit (Over.mapPullbackAdj (g ≫ f))
      ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f)) (Over.mapComp g f).inv U.obj
  simpa [Adjunction.comp_counit_app, Over.mapComp, Category.assoc] using
    congrArg Over.Hom.left hc

/-- The underlying morphism of schemes of the canonical lift through base change. -/
public theorem smallEtaleBaseChangeLift_left {S' T' : B.Scheme} (h : T' ⟶ S')
    (U : SmallEtale B S'.1 S'.property) (V : SmallEtale B T'.1 T'.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ h) :
    (smallEtaleBaseChangeLift B h U V k hk).hom.left = pullback.lift k V.obj.hom hk := rfl

/-- The underlying morphism of schemes of a base-changed morphism. -/
public theorem smallEtaleBaseChange_map_left {S' T' : B.Scheme} (h : T' ⟶ S')
    {X Y : SmallEtale B S'.1 S'.property} (a : X ⟶ Y) :
    ((smallEtaleBaseChange B h).map a).hom.left =
      pullback.lift (f := Y.obj.hom) (g := h)
        (pullback.fst X.obj.hom h ≫ a.hom.left) (pullback.snd X.obj.hom h)
        (by simp [pullback.condition]) := rfl

/-- The structure morphism of a base-changed object is the second projection. -/
public theorem smallEtaleBaseChange_obj_hom {S' T' : B.Scheme} (h : T' ⟶ S')
    (X : SmallEtale B S'.1 S'.property) :
    ((smallEtaleBaseChange B h).obj X).obj.hom = pullback.snd X.obj.hom h := rfl

/-- The second projection of the comparison of two successive base changes with base change
along the composite. -/
public theorem smallBaseChangeComp_inv_snd
    {T T' T'' : B.Scheme} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : SmallEtale B T.1 T.property) :
    ((smallEtaleBaseChange_compIso B T'' T' T g f).val.inv.app U).hom.left ≫
        pullback.snd (pullback.snd U.obj.hom f) g = pullback.snd U.obj.hom (g ≫ f) :=
  ((smallEtaleBaseChange_compIso B T'' T' T g f).val.inv.app U).hom.w

/-- The underlying computation behind the compatibility of canonical lifts with composition:
any morphism into the iterated fibre product with the two projections of the comparison is the
comparison of the lifts. -/
public theorem smallEtaleBaseChangeLift_comp_left
    {T T' T'' : B.Scheme} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : SmallEtale B T.1 T.property) (V : SmallEtale B T'.1 T'.property)
    (W : SmallEtale B T''.1 T''.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f)
    (l : W.obj.left ⟶ V.obj.left) (hl : l ≫ V.obj.hom = W.obj.hom ≫ g)
    (h₁ : (l ≫ k) ≫ U.obj.hom = W.obj.hom ≫ g ≫ f)
    (h₂ : (pullback.fst V.obj.hom g ≫ pullback.lift k V.obj.hom hk) ≫
      pullback.snd U.obj.hom f = pullback.snd V.obj.hom g ≫ g)
    (m : pullback U.obj.hom (g ≫ f) ⟶ pullback (pullback.snd U.obj.hom f) g)
    (hm₁ : m ≫ pullback.fst (pullback.snd U.obj.hom f) g ≫ pullback.fst U.obj.hom f =
      pullback.fst U.obj.hom (g ≫ f))
    (hm₂ : m ≫ pullback.snd (pullback.snd U.obj.hom f) g =
      pullback.snd U.obj.hom (g ≫ f)) :
    pullback.lift (l ≫ k) W.obj.hom h₁ ≫ m =
      pullback.lift l W.obj.hom hl ≫
        pullback.lift (pullback.fst V.obj.hom g ≫ pullback.lift k V.obj.hom hk)
          (pullback.snd V.obj.hom g) h₂ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hm₁, pullback.lift_fst]
      simp only [Category.assoc]
      rw [pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% hm₂, pullback.lift_snd_assoc,
        pullback.lift_snd_assoc, pullback.lift_snd_assoc]
  · simp only [Category.assoc]
    rw [hm₂, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

/-- The sections of a compatible system over `U`, restricted along a morphism of schemes over
the base covering `f`. This is the strictly functorial description of the reconstruction. -/
public def sectionMap (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
    (U : SmallEtale B T.left.1 T.left.property)
    (V : SmallEtale B T'.left.1 T'.left.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left) :
    (D.sheaf T).obj.obj (op U) ⟶ (D.sheaf T').obj.obj (op V) :=
  (dataPushforwardMap B S hS D f).hom.app (op U) ≫
    (D.sheaf T').obj.map (smallEtaleBaseChangeLift B f.left U V k hk).op

public theorem smallEtaleBaseChangeLift_comp
    {T T' T'' : B.Scheme} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : SmallEtale B T.1 T.property) (V : SmallEtale B T'.1 T'.property)
    (W : SmallEtale B T''.1 T''.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f)
    (l : W.obj.left ⟶ V.obj.left) (hl : l ≫ V.obj.hom = W.obj.hom ≫ g) :
    smallEtaleBaseChangeLift B (g ≫ f) U W (l ≫ k)
          (by simp [Category.assoc, hk, reassoc_of% hl]) ≫
        (smallEtaleBaseChange_compIso B T'' T' T g f).val.inv.app U =
      smallEtaleBaseChangeLift B g V W l hl ≫
        (smallEtaleBaseChange B g).map (smallEtaleBaseChangeLift B f U V k hk) := by
  apply (SmallEtale.inclusion B T''.1 T''.property).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, ObjectProperty.ι_map, smallEtaleBaseChangeLift_left,
    smallEtaleBaseChange_map_left]
  exact smallEtaleBaseChangeLift_comp_left B f g U V W k hk l hl _ _ _
    (smallBaseChangeComp_inv_fst B f g U) (smallBaseChangeComp_inv_snd B f g U)

public theorem sectionMap_comp (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' T'' : BigEtaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : SmallEtale B T.left.1 T.left.property)
    (V : SmallEtale B T'.left.1 T'.left.property)
    (W : SmallEtale B T''.left.1 T''.left.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left)
    (l : W.obj.left ⟶ V.obj.left) (hl : l ≫ V.obj.hom = W.obj.hom ≫ g.left) :
    sectionMap B S hS D f U V k hk ≫ sectionMap B S hS D g V W l hl =
      sectionMap B S hS D (g ≫ f) U W (l ≫ k)
        (by simp [Category.assoc, hk, reassoc_of% hl]) := by
  have hc := congrArg (fun q => q.hom.app (op U))
    (dataPushforwardMap_comp B S hS D f g)
  let af := smallEtaleBaseChangeLift B f.left U V k hk
  let ag := smallEtaleBaseChangeLift B g.left V W l hl
  let agf := smallEtaleBaseChangeLift B (g ≫ f).left U W (l ≫ k)
    (by simp [Category.assoc, hk, reassoc_of% hl])
  let δ := (smallEtaleBaseChange_compIso B T''.left T'.left T.left
    g.left f.left).val.inv.app U
  let qf : (D.sheaf T).obj.obj (op U) ⟶
      (D.sheaf T').obj.obj (op ((smallEtaleBaseChange B f.left).obj U)) :=
    (dataPushforwardMap B S hS D f).hom.app (op U)
  let qg : (D.sheaf T').obj.obj (op ((smallEtaleBaseChange B f.left).obj U)) ⟶
      (D.sheaf T'').obj.obj (op ((smallEtaleBaseChange B g.left).obj
        ((smallEtaleBaseChange B f.left).obj U))) :=
    (dataPushforwardMap B S hS D g).hom.app
      (op ((smallEtaleBaseChange B f.left).obj U))
  let qgV : (D.sheaf T').obj.obj (op V) ⟶
      (D.sheaf T'').obj.obj (op ((smallEtaleBaseChange B g.left).obj V)) :=
    (dataPushforwardMap B S hS D g).hom.app (op V)
  let qgf : (D.sheaf T).obj.obj (op U) ⟶
      (D.sheaf T'').obj.obj (op ((smallEtaleBaseChange B (g ≫ f).left).obj U)) :=
    (dataPushforwardMap B S hS D (g ≫ f)).hom.app (op U)
  let mAf := (D.sheaf T').obj.map af.op
  let mAg := (D.sheaf T'').obj.map ag.op
  let mAgf := (D.sheaf T'').obj.map agf.op
  let mGaf := (D.sheaf T'').obj.map ((smallEtaleBaseChange B g.left).map af).op
  let mδ := (D.sheaf T'').obj.map δ.op
  have hc' : qf ≫ qg ≫ mδ = qgf := hc
  have hn : mAf ≫ qgV = qg ≫ mGaf :=
    (dataPushforwardMap B S hS D g).hom.naturality af.op
  have hm : mGaf ≫ mAg = mδ ≫ mAgf := by
    dsimp only [mGaf, mAg, mδ, mAgf]
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    exact congrArg (D.sheaf T'').obj.map
      (congrArg Quiver.Hom.op
        (smallEtaleBaseChangeLift_comp B f.left g.left U V W k hk l hl).symm)
  exact comp_eq_of_comm_squares hc' hn hm

public theorem reconstructedSmallSectionsMap_eq_sectionMap
    (D : BigEtaleSheafData.{u, v} B S hS) (T : BigEtaleOver B S hS)
    (U : SmallEtale B T.left.1 T.left.property) :
    reconstructedSmallSectionsMap B S hS D T U =
      sectionMap B S hS D (smallStructureArrow B S hS T U) U
        (smallEtaleTerminal B S hS
          ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).obj U))
        (𝟙 _) (by simp [smallStructureArrow, smallEtaleTerminal, SmallEtale.final]) := by
  let r := smallStructureArrow B S hS T U
  have : Etale (B.inclusion.map r.left) := U.property
  have h := smallInverseImageIsoPostcomposePushforward_inv_app_comp B r.left
    (D.sheaf T) (D.sheaf _) (D.pullback r)
    (smallEtaleTerminal B S hS
      ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).obj U))
  rwa [smallEtalePostcomposeBaseChangeAdjunction_unit_app] at h

/-- The canonical lift through base change absorbs a morphism of the small étale site. -/
public theorem smallEtaleBaseChangeLift_precomp {S' T' : B.Scheme} (h : T' ⟶ S')
    {U V : SmallEtale B S'.1 S'.property} (a : U ⟶ V)
    (W : SmallEtale B T'.1 T'.property)
    (k : W.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = W.obj.hom ≫ h) :
    smallEtaleBaseChangeLift B h U W k hk ≫ (smallEtaleBaseChange B h).map a =
      smallEtaleBaseChangeLift B h V W (k ≫ a.hom.left)
        (by rw [Category.assoc, a.hom.w, hk]) := by
  apply (SmallEtale.inclusion B T'.1 T'.property).map_injective
  rw [Functor.map_comp]
  apply Over.OverMorphism.ext
  simp only [SmallEtale.inclusion, ObjectProperty.ι_obj, Over.comp_left,
    ObjectProperty.ι_map, smallEtaleBaseChangeLift_left, smallEtaleBaseChange_map_left]
  apply pullback.hom_ext
  · simp only [SmallEtale.inclusion, ObjectProperty.ι_obj, Category.assoc]
    rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [SmallEtale.inclusion, ObjectProperty.ι_obj, Category.assoc]
    rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

public theorem sectionMap_precomp (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
    {U V : SmallEtale B T.left.1 T.left.property} (a : U ⟶ V)
    (W : SmallEtale B T'.left.1 T'.left.property)
    (k : W.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = W.obj.hom ≫ f.left) :
    (D.sheaf T).obj.map a.op ≫ sectionMap B S hS D f U W k hk =
      sectionMap B S hS D f V W (k ≫ a.hom.left)
        (by rw [Category.assoc, a.hom.w, hk]) := by
  dsimp only [sectionMap]
  rw [← Category.assoc ((D.sheaf T).obj.map a.op)
      ((dataPushforwardMap B S hS D f).hom.app (op U)),
    (dataPushforwardMap B S hS D f).hom.naturality]
  show (_ ≫ (D.sheaf T').obj.map
    ((smallEtaleBaseChange B f.left).map a).op) ≫ _ = _
  rw [Category.assoc, ← Functor.map_comp, ← op_comp]
  congr 2
  exact congrArg Quiver.Hom.op (smallEtaleBaseChangeLift_precomp B f.left a W k hk)

public theorem reconstructedPresheafMap_eq_sectionMap
    (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    reconstructedPresheafMap B S hS D f =
      sectionMap B S hS D f (smallEtaleTerminal B S hS T)
        (smallEtaleTerminal B S hS T') f.left (by
          simp [smallEtaleTerminal, SmallEtale.final]) := by
  dsimp only [reconstructedPresheafMap, sectionMap]
  congr 2
  apply congrArg Quiver.Hom.op
  apply ((SmallEtale.finalIsTerminal B T.left.1 T.left.property).isTerminalObj
    (smallEtaleBaseChange B f.left)).hom_ext

public theorem reconstructedSmallSectionsMap_naturality
    (D : BigEtaleSheafData.{u, v} B S hS) (T : BigEtaleOver B S hS)
    {U V : SmallEtale B T.left.1 T.left.property} (k : U ⟶ V) :
    (D.sheaf T).1.map k.op ≫ reconstructedSmallSectionsMap B S hS D T U =
      reconstructedSmallSectionsMap B S hS D T V ≫
        (reconstructedPresheaf B S hS D).map
          ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).map k).op := by
  show _ = _ ≫ reconstructedPresheafMap B S hS D _
  simp only [Quiver.Hom.unop_op]
  rw [reconstructedPresheafMap_eq_sectionMap,
    reconstructedSmallSectionsMap_eq_sectionMap,
    reconstructedSmallSectionsMap_eq_sectionMap]
  refine Eq.trans
    (sectionMap_precomp B S hS D (smallStructureArrow B S hS T U) k _ _ _) ?_
  rw [sectionMap_comp]
  have hcomp :
      (smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).map k ≫
        smallStructureArrow B S hS T V = smallStructureArrow B S hS T U :=
    Over.OverMorphism.ext k.hom.w
  simp only [hcomp, Category.id_comp, Category.comp_id]
  rfl

/-- Restriction of a big étale sheaf to the small étale sites is compatible with base change,
in the direct-image form. -/
public def restrictionPushforwardMap
    (F : Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    (bigEtaleSheafRestrictionAt B S hS T).obj F ⟶
      (B.smallPushforward f.left (Type (max (u + 1) v))).obj
        ((bigEtaleSheafRestrictionAt B S hS T').obj F) :=
  ObjectProperty.homMk {
    app U := F.obj.map (bigEtaleBaseChangeProjection B S hS f U.unop).op
    naturality {U V} k := by
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      apply congrArg F.obj.map
      simp only [Functor.op_map, Quiver.Hom.unop_op]
      rw [← op_comp, ← op_comp]
      apply congrArg Quiver.Hom.op
      apply Over.OverMorphism.ext
      simp only [bigEtaleBaseChangeProjection, smallEtaleToBigEtaleFunctor,
        Over.comp_left, Over.homMk_left, Functor.comp_map, ObjectProperty.ι_map,
        Over.map_map_left, smallEtaleBaseChange_map_left]
      rw [pullback.lift_fst] }

public theorem restrictionPushforwardMap_comp
    (F : Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' T'' : BigEtaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    restrictionPushforwardMap B S hS F f ≫
      (B.smallPushforward f.left (Type (max (u + 1) v))).map
          (restrictionPushforwardMap B S hS F g) ≫
        (smallPushforwardCompIso B S hS f g).hom.app
          ((bigEtaleSheafRestrictionAt B S hS T'').obj F) =
      restrictionPushforwardMap B S hS F (g ≫ f) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  show F.obj.map (bigEtaleBaseChangeProjection B S hS f U.unop).op ≫
      F.obj.map (bigEtaleBaseChangeProjection B S hS g
        ((smallEtaleBaseChange B f.left).obj U.unop)).op ≫
      F.obj.map ((smallEtaleToBigEtaleFunctor B T''.left (B.obj S hS) T''.hom).map
        ((smallEtaleBaseChange_compIso B T''.left T'.left T.left
          g.left f.left).val.inv.app U.unop)).op =
    F.obj.map (bigEtaleBaseChangeProjection B S hS (g ≫ f) U.unop).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  apply congrArg F.obj.map
  apply congrArg Quiver.Hom.op
  apply Over.OverMorphism.ext
  exact smallBaseChangeComp_inv_fst B f.left g.left U.unop


public theorem pullback_comp_of_pushforward_comp
    {T T' T'' : BigEtaleOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (F : Sheaf (SmallEtale.topology B T.left.1 T.left.property) (Type (max (u + 1) v)))
    (G : Sheaf (SmallEtale.topology B T'.left.1 T'.left.property) (Type (max (u + 1) v)))
    (H : Sheaf (SmallEtale.topology B T''.left.1 T''.left.property) (Type (max (u + 1) v)))
    (a : F ⟶ (B.smallPushforward f.left (Type (max (u + 1) v))).obj G)
    (b : G ⟶ (B.smallPushforward g.left (Type (max (u + 1) v))).obj H)
    (c : F ⟶ (B.smallPushforward (g ≫ f).left (Type (max (u + 1) v))).obj H)
    (h : a ≫ (B.smallPushforward f.left (Type (max (u + 1) v))).map b ≫
      (smallPushforwardCompIso B S hS f g).hom.app H = c) :
    (B.smallInverseImage g.left (Type (max (u + 1) v))).map
        ((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _ |>.symm a) ≫
      ((B.smallPullbackAdjunction g.left (Type (max (u + 1) v))).homEquiv _ _).symm b =
      (smallInverseImageCompIso B S hS f g).hom.app F ≫
        ((B.smallPullbackAdjunction (g ≫ f).left
          (Type (max (u + 1) v))).homEquiv _ _).symm c := by
  let adj₁ := B.smallPullbackAdjunction f.left (Type (max (u + 1) v))
  let adj₂ := B.smallPullbackAdjunction g.left (Type (max (u + 1) v))
  let adj₃ := B.smallPullbackAdjunction (g ≫ f).left (Type (max (u + 1) v))
  let e := smallPushforwardCompIso B S hS f g
  let adj := (adj₁.comp adj₂).ofNatIsoRight e
  apply (adj.homEquiv _ _).injective
  rw [smallInverseImageCompIso_eq_leftAdjointUniq,
    Adjunction.homEquiv_leftAdjointUniq_hom_app_comp]
  show adj.homEquiv _ _ ((B.smallInverseImage g.left (Type (max (u + 1) v))).map
    ((adj₁.homEquiv _ _).symm a) ≫
    (adj₂.homEquiv _ _).symm b) = adj₃.homEquiv _ _ ((adj₃.homEquiv _ _).symm c)
  dsimp only [adj]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  show adj₁.homEquiv _ _ (adj₂.homEquiv _ _
    ((B.smallInverseImage g.left (Type (max (u + 1) v))).map
      ((adj₁.homEquiv _ _).symm a) ≫
      (adj₂.homEquiv _ _).symm b)) ≫ e.hom.app H = _
  rw [adj₂.homEquiv_naturality_left, adj₁.homEquiv_naturality_right]
  simpa only [Equiv.apply_symm_apply, Category.assoc] using h

/-- The comparison map on restrictions of a big étale sheaf, in the inverse-image form. -/
public def restrictionPullbackMap
    (F : Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    (B.smallInverseImage f.left (Type (max (u + 1) v))).obj
        ((bigEtaleSheafRestrictionAt B S hS T).obj F) ⟶
      (bigEtaleSheafRestrictionAt B S hS T').obj F :=
  ((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _).symm
    (restrictionPushforwardMap B S hS F f)

public theorem restrictionPullbackMap_isIso
    (F : Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) [Etale (B.inclusion.map f.left)] :
    IsIso (restrictionPullbackMap B S hS F f) := by
  let adj := smallEtalePostcomposePushforwardAdjunction B f.left (Type (max (u + 1) v))
  let e := smallInverseImageIsoPostcomposePushforward B f.left (Type (max (u + 1) v))
  have he : e.inv.app ((bigEtaleSheafRestrictionAt B S hS T).obj F) ≫
      restrictionPullbackMap B S hS F f =
      (adj.homEquiv _ _).symm (restrictionPushforwardMap B S hS F f) := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    show adj.homEquiv _ _
      ((Adjunction.leftAdjointUniq
        (B.smallPullbackAdjunction f.left (Type (max (u + 1) v))) adj).inv.app _ ≫ _) = _
    rw [Adjunction.leftAdjointUniq_inv_app,
      Adjunction.homEquiv_leftAdjointUniq_hom_app_comp]
    exact Equiv.apply_symm_apply _ _
  have hi : IsIso ((adj.homEquiv _ _).symm (restrictionPushforwardMap B S hS F f)) := by
    refine @isIso_of_reflects_iso _ _ _ _ _ _ _ (sheafToPresheaf _ _) ?_ inferInstance
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro U
    show IsIso (((adj.homEquiv _ _).symm
      (restrictionPushforwardMap B S hS F f)).hom.app U)
    rw [Adjunction.homEquiv_symm_apply]
    show IsIso ((restrictionPushforwardMap B S hS F f).hom.app
      (op ((smallEtalePostcompose B T.left.1 T.left.property
        (SmallEtale.ofEtaleHom B f.left)).obj U.unop)) ≫
      (adj.counit.app ((bigEtaleSheafRestrictionAt B S hS T').obj F)).hom.app U)
    rw [smallEtalePostcomposePushforwardAdjunction_counit_app,
      smallEtalePostcomposeBaseChangeAdjunction_unit_app]
    show IsIso (F.obj.map _ ≫ F.obj.map _)
    simp only [Functor.op_map, Quiver.Hom.unop_op]
    rw [← Functor.map_comp, ← op_comp]
    have : IsIso
        ((smallEtaleToBigEtaleFunctor B T'.left (B.obj S hS) T'.hom).map
            (smallEtaleBaseChangeLift B f.left
              ((smallEtalePostcompose B T.left.1 T.left.property
                (SmallEtale.ofEtaleHom B f.left)).obj U.unop)
              U.unop (𝟙 _) (by simp [smallEtalePostcompose])) ≫
          bigEtaleBaseChangeProjection B S hS f
            ((smallEtalePostcompose B T.left.1 T.left.property
              (SmallEtale.ofEtaleHom B f.left)).obj U.unop)) := by
      refine @isIso_of_reflects_iso _ _ _ _ _ _ _ (Over.forget (B.obj S hS)) ?_ inferInstance
      show IsIso (pullback.lift (𝟙 _) U.unop.obj.hom _ ≫ pullback.fst _ _)
      convert IsIso.id (U.unop.obj.left) using 1
      exact pullback.lift_fst _ _ _
    infer_instance
  have : IsIso (e.inv.app ((bigEtaleSheafRestrictionAt B S hS T).obj F) ≫
      restrictionPullbackMap B S hS F f) := he ▸ hi
  have hfac : restrictionPullbackMap B S hS F f =
      e.hom.app ((bigEtaleSheafRestrictionAt B S hS T).obj F) ≫
        (e.inv.app ((bigEtaleSheafRestrictionAt B S hS T).obj F) ≫
          restrictionPullbackMap B S hS F f) := by simp
  rw [hfac]
  infer_instance

/-- The compatible system of small étale sheaves obtained by restricting a sheaf on the big
étale site over `S`. -/
public def restrictionData
    (F : Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v))) :
    BigEtaleSheafData.{u, v} B S hS where
  sheaf T := (bigEtaleSheafRestrictionAt B S hS T).obj F
  pullback f := restrictionPullbackMap B S hS F f
  pullback_comp f g := pullback_comp_of_pushforward_comp B S hS f g _ _ _ _ _ _
    (restrictionPushforwardMap_comp B S hS F f g)
  isIso_pullback f := restrictionPullbackMap_isIso B S hS F f

public def reconstructedSmallSectionsIso
    (D : BigEtaleSheafData.{u, v} B S hS) (T : BigEtaleOver B S hS) :
    (D.sheaf T).1 ≅
      (smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).op ⋙
        reconstructedPresheaf B S hS D := by
  haveI (U : SmallEtale B T.left.1 T.left.property) :
      IsIso (reconstructedSmallSectionsMap B S hS D T U) :=
    reconstructedSmallSectionsMap_isIso B S hS D T U
  exact NatIso.ofComponents
    (fun U => asIso (reconstructedSmallSectionsMap B S hS D T U.unop))
    (fun {U V} k => reconstructedSmallSectionsMap_naturality B S hS D T k.unop)

public theorem reconstructedPresheaf_small_isSheaf
    (D : BigEtaleSheafData.{u, v} B S hS) (T : BigEtaleOver B S hS) :
    Presieve.IsSheaf (SmallEtale.topology B T.left.1 T.left.property)
      ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).op ⋙
        reconstructedPresheaf B S hS D) :=
  Presieve.isSheaf_iso _ (reconstructedSmallSectionsIso B S hS D T)
    ((isSheaf_iff_isSheaf_of_type _ _).mp (D.sheaf T).property)

public theorem reconstructedPresheaf_isSheafFor_bigCover
    (P : (BigEtaleOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v))
    (H : ∀ T : BigEtaleOver B S hS,
      Presieve.IsSheaf (SmallEtale.topology B T.left.1 T.left.property)
        ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).op ⋙ P))
    (T : BigEtaleOver B S hS) (E : PreZeroHypercover.{u + 1} T)
    (hE : BigEtaleOver.IsCovering B S hS ⟨T, E⟩) :
    Presieve.IsSheafFor P E.presieve₀ := by
  let j := smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom
  have hcover := BigEtaleSite.IsCovering.etale (B := B) hE
  change (E.map (BigEtaleOver.toScheme B S hS)).presieve₀ ∈
    Scheme.etalePrecoverage _ at hcover
  simp only [Scheme.etalePrecoverage] at hcover
  have hEtale (i : E.I₀) :
      Etale ((BigEtaleOver.toScheme B S hS).map (E.f i)) := hcover.2 ⟨i⟩
  let Y (i : E.I₀) : SmallEtale B T.left.1 T.left.property :=
    ⟨Over.mk (E.f i).left, by
      show Etale (B.inclusion.map (E.f i).left)
      simpa [BigEtaleOver.toScheme] using hEtale i⟩
  let A := smallEtaleTerminal B S hS T
  let q (i : E.I₀) : Y i ⟶ A :=
    ObjectProperty.homMk (Over.homMk (E.f i).left)
  let E' : PreZeroHypercover.{u + 1} A := ⟨E.I₀, Y, q⟩
  have hE' : SmallEtale.IsCovering B T.left.1 T.left.property ⟨A, E'⟩ := by
    show BigEtaleOver.IsCovering B T.left.1 T.left.property
      ⟨(SmallEtale.inclusion B T.left.1 T.left.property).obj A,
        E'.map (SmallEtale.inclusion B T.left.1 T.left.property)⟩
    let k := SmallEtale.inclusion B T.left.1 T.left.property ⋙
      Over.forget (B.obj T.left.1 T.left.property)
    have hmap : E'.map k = E.map (Over.forget (B.obj S hS)) := by
      ext <;> rfl
    show B.IsCovering ⟨T.left, E'.map k⟩
    change B.IsCovering ⟨T.left, E.map (Over.forget (B.obj S hS))⟩ at hE
    rw [hmap]
    exact hE
  have hp := (H T).isSheafFor_of_mem_precoverage
    ((SmallEtale.mem_precoverage_iff _ _ _).mpr ⟨E', rfl, hE'⟩)
  have : PreservesLimitsOfShape WalkingCospan (j ⋙ BigEtaleOver.toScheme B S hS) := by
    show PreservesLimitsOfShape WalkingCospan
      (SmallEtale.toScheme B T.left.1 T.left.property)
    exact preservesPullbacks_smallEtaleToScheme B T.left.1 T.left.property
  have : PreservesLimitsOfShape WalkingCospan j := by
    have : PreservesLimitsOfShape WalkingCospan
        ((j ⋙ Over.forget (B.obj S hS)) ⋙ B.inclusion) := by
      simpa only [Functor.assoc] using
        (show PreservesLimitsOfShape WalkingCospan
          (j ⋙ BigEtaleOver.toScheme B S hS) from inferInstance)
    have hforget : PreservesLimitsOfShape WalkingCospan
        (j ⋙ Over.forget (B.obj S hS)) := by
      have : ReflectsLimitsOfShape WalkingCospan B.inclusion :=
        (fullyFaithful_reflectsLimits B.inclusion).reflectsLimitsOfShape
      exact preservesLimitsOfShape_of_reflects_of_preserves
        (j ⋙ Over.forget (B.obj S hS)) B.inclusion
    exact preservesLimitsOfShape_of_reflects_of_preserves j
      (Over.forget (B.obj S hS))
  have hp' := (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks
    j P E'.presieve₀).mp hp
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hp'
  let e : j.obj A ≅ T := Over.isoMk (Iso.refl _) (by
    simp [A, j, smallEtaleToBigEtaleFunctor, smallEtaleTerminal, SmallEtale.final])
  have hp'' := (isSheafFor_postcomp_iso P (fun i => j.map (q i)) e).mp hp'
  let eY (i : E.I₀) : j.obj (Y i) ≅ E.X i :=
    Over.isoMk (Iso.refl _) (by simp [j, Y, smallEtaleToBigEtaleFunctor])
  have heq (i : E.I₀) : j.map (q i) ≫ e.hom = (eY i).hom ≫ E.f i := by
    apply Over.OverMorphism.ext
    simp [e, eY, q, j, smallEtaleToBigEtaleFunctor]
  simp only [heq] at hp''
  exact (Presieve.isSheafFor_ofArrows_comp_iff E.f eY).mp hp''

public theorem reconstructedPresheaf_isSheaf_of_small_restrictions
    (P : (BigEtaleOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v))
    (H : ∀ T : BigEtaleOver B S hS,
      Presieve.IsSheaf (SmallEtale.topology B T.left.1 T.left.property)
        ((smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).op ⋙ P)) :
    Presieve.IsSheaf (BigEtaleOver.topology B S hS) P := by
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  obtain ⟨E, rfl, hE⟩ := (BigEtaleOver.mem_precoverage_iff _ _ _).mp hR
  obtain ⟨Q, p, q, hpq, hQ⟩ := B.coverings_isSite.2.2
    ⟨X.left, E.map (Over.forget (B.obj S hS))⟩ hE Y.left f.left
  let Z (i : E.I₀) : BigEtaleOver B S hS := Over.mk (q i ≫ Y.hom)
  let a (i : E.I₀) : Z i ⟶ E.X i := Over.homMk (p i) (by
    have hi : p i ≫ (E.f i).left = q i ≫ f.left := (hpq i).w
    show p i ≫ (E.X i).hom = q i ≫ Y.hom
    calc p i ≫ (E.X i).hom = p i ≫ (E.f i).left ≫ X.hom :=
          congrArg (fun z => p i ≫ z) (Over.w (E.f i)).symm
      _ = (p i ≫ (E.f i).left) ≫ X.hom := (Category.assoc _ _ _).symm
      _ = (q i ≫ f.left) ≫ X.hom := congrArg (fun z => z ≫ X.hom) hi
      _ = q i ≫ f.left ≫ X.hom := Category.assoc _ _ _
      _ = q i ≫ Y.hom := congrArg (fun z => q i ≫ z) (Over.w f))
  let b (i : E.I₀) : Z i ⟶ Y := Over.homMk (q i)
  have hp (i : E.I₀) : IsPullback (a i) (b i) (E.f i) f :=
    IsPullback.of_map (Over.forget (B.obj S hS)) (Over.OverMorphism.ext (hpq i).w) (hpq i)
  let E' : PreZeroHypercover.{u + 1} Y := ⟨E.I₀, Z, b⟩
  have hE' : BigEtaleOver.IsCovering B S hS ⟨Y, E'⟩ := hQ
  have hsheaf := reconstructedPresheaf_isSheafFor_bigCover
    B S hS P H Y E' hE'
  rw [Presieve.isSheafFor_iff_generate] at hsheaf
  change Presieve.IsSheafFor P (Sieve.ofArrows Z b).arrows at hsheaf
  rwa [Sieve.ofArrows_eq_pullback_of_isPullback E.f (fun i => (hp i).flip)] at hsheaf

/-- The sheaf on the big étale site over `S` reconstructed from a compatible system. -/
public def reconstructedSheaf (D : BigEtaleSheafData.{u, v} B S hS) :
    Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)) :=
  ⟨reconstructedPresheaf B S hS D,
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (reconstructedPresheaf_isSheaf_of_small_restrictions B S hS
        (reconstructedPresheaf B S hS D)
        (reconstructedPresheaf_small_isSheaf B S hS D))⟩

public def reconstructedSheafFunctor : BigEtaleSheafData.{u, v} B S hS ⥤
    Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)) where
  obj := reconstructedSheaf B S hS
  map φ := ObjectProperty.homMk ((reconstructedPresheafFunctor B S hS).map φ)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Stacks Project, Tag 021K.** Restriction of a sheaf on the big étale site over `S` to the
small étale sites of all schemes over `S`, as a functor to compatible systems. -/
public def bigEtaleSheafRestriction :
    Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)) ⥤
      BigEtaleSheafData.{u, v} B S hS where
  obj := restrictionData B S hS
  map φ := {
    app T := (bigEtaleSheafRestrictionAt B S hS T).map φ
    naturality {T T'} f := by
      apply ((B.smallPullbackAdjunction f.left
        (Type (max (u + 1) v))).homEquiv _ _).injective
      change (B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _
        ((B.smallInverseImage f.left (Type (max (u + 1) v))).map _ ≫
          restrictionPullbackMap B S hS _ f) =
        (B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _
          (restrictionPullbackMap B S hS _ f ≫ _)
      rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
      dsimp only [restrictionPullbackMap]
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      exact (φ.hom.naturality (bigEtaleBaseChangeProjection B S hS f U.unop).op).symm }
  map_id F := by
    apply BigEtaleSheafData.Hom.ext
    intro T
    exact (bigEtaleSheafRestrictionAt B S hS T).map_id F
  map_comp φ ψ := by
    apply BigEtaleSheafData.Hom.ext
    intro T
    exact (bigEtaleSheafRestrictionAt B S hS T).map_comp φ ψ

public theorem sectionMap_baseChange
    (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
    (U : SmallEtale B T.left.1 T.left.property) :
    sectionMap B S hS D f U ((smallEtaleBaseChange B f.left).obj U)
      (pullback.fst U.obj.hom f.left) pullback.condition =
      (dataPushforwardMap B S hS D f).hom.app (op U) := by
  have h : smallEtaleBaseChangeLift B f.left U ((smallEtaleBaseChange B f.left).obj U)
      (pullback.fst U.obj.hom f.left) pullback.condition = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [smallEtaleBaseChangeLift]
  have hm : (D.sheaf T').obj.map
      (smallEtaleBaseChangeLift B f.left U ((smallEtaleBaseChange B f.left).obj U)
        (pullback.fst U.obj.hom f.left) pullback.condition).op = 𝟙 _ := by
    rw [h]
    exact (D.sheaf T').obj.map_id _
  exact (congrArg (fun a => (dataPushforwardMap B S hS D f).hom.app (op U) ≫ a) hm).trans
    (Category.comp_id _)

public theorem reconstructedSmallSectionsMap_transition
    (D : BigEtaleSheafData.{u, v} B S hS)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
    (U : SmallEtale B T.left.1 T.left.property) :
    reconstructedSmallSectionsMap B S hS D T U ≫
        (reconstructedPresheaf B S hS D).map
          (bigEtaleBaseChangeProjection B S hS f U).op =
      (dataPushforwardMap B S hS D f).hom.app (op U) ≫
        reconstructedSmallSectionsMap B S hS D T'
          ((smallEtaleBaseChange B f.left).obj U) := by
  show _ ≫ reconstructedPresheafMap B S hS D _ = _
  simp only [Quiver.Hom.unop_op]
  rw [reconstructedSmallSectionsMap_eq_sectionMap,
    reconstructedSmallSectionsMap_eq_sectionMap,
    reconstructedPresheafMap_eq_sectionMap, ← sectionMap_baseChange]
  simp only [sectionMap_comp]
  have hcomp : bigEtaleBaseChangeProjection B S hS f U ≫ smallStructureArrow B S hS T U =
      smallStructureArrow B S hS T' ((smallEtaleBaseChange B f.left).obj U) ≫ f :=
    Over.OverMorphism.ext pullback.condition
  refine Eq.trans ?_ (sectionMap_comp B S hS D f
    (smallStructureArrow B S hS T' ((smallEtaleBaseChange B f.left).obj U)) U
    ((smallEtaleBaseChange B f.left).obj U)
    (smallEtaleTerminal B S hS
      ((smallEtaleToBigEtaleFunctor B T'.left (B.obj S hS) T'.hom).obj
        ((smallEtaleBaseChange B f.left).obj U)))
    (pullback.fst U.obj.hom f.left) pullback.condition (𝟙 _)
    (by simp [smallStructureArrow, smallEtaleTerminal, SmallEtale.final])).symm
  simp only [hcomp, Category.id_comp, Category.comp_id]
  rfl

public def reconstructedSmallIso
    (D : BigEtaleSheafData.{u, v} B S hS) (T : BigEtaleOver B S hS) :
    D.sheaf T ≅ (bigEtaleSheafRestrictionAt B S hS T).obj (reconstructedSheaf B S hS D) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (reconstructedSmallSectionsIso B S hS D T)

-- Recognizing the restriction of a reconstructed sheaf as the sheaf the system assigns is a
-- round trip through the structure projections of the compatible data.
attribute [local implicit_reducible] restrictionData reconstructedPresheaf reconstructedSheaf
  reconstructedPresheafMap

public def reconstructionDataHom (D : BigEtaleSheafData.{u, v} B S hS) :
    D ⟶ restrictionData B S hS (reconstructedSheaf B S hS D) where
  app T := (reconstructedSmallIso B S hS D T).hom
  naturality {T T'} f := by
    apply ((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    change _ ≫ (B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _
      (restrictionPullbackMap B S hS _ f) = _
    dsimp only [restrictionPullbackMap]
    rw [Equiv.apply_symm_apply]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact reconstructedSmallSectionsMap_transition B S hS D f U.unop

public theorem dataHom_isIso_of_app
    {D E : BigEtaleSheafData.{u, v} B S hS} (φ : D ⟶ E)
    (h : ∀ T, IsIso (φ.app T)) : IsIso φ := by
  have := h
  let ψ : E ⟶ D := {
    app T := inv (φ.app T)
    naturality {T T'} f := by
      apply (cancel_mono (φ.app T')).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← φ.naturality f, ← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
        (B.smallInverseImage f.left (Type (max (u + 1) v))).map_id, Category.id_comp] }
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · apply BigEtaleSheafData.Hom.ext
    intro T
    show φ.app T ≫ inv (φ.app T) = 𝟙 _
    exact IsIso.hom_inv_id _
  · apply BigEtaleSheafData.Hom.ext
    intro T
    show inv (φ.app T) ≫ φ.app T = 𝟙 _
    exact IsIso.inv_hom_id _

public theorem sectionMap_hom_naturality
    {D E : BigEtaleSheafData.{u, v} B S hS} (φ : D ⟶ E)
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
    (U : SmallEtale B T.left.1 T.left.property)
    (V : SmallEtale B T'.left.1 T'.left.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f.left) :
    (φ.app T).hom.app (op U) ≫ sectionMap B S hS E f U V k hk =
      sectionMap B S hS D f U V k hk ≫ (φ.app T').hom.app (op V) := by
  have hq := congrArg (fun q => q.hom.app (op U))
    (dataPushforwardMap_hom_naturality B S hS φ f)
  change (φ.app T).hom.app (op U) ≫ (dataPushforwardMap B S hS E f).hom.app (op U) =
    (dataPushforwardMap B S hS D f).hom.app (op U) ≫
      (φ.app T').hom.app (op ((smallEtaleBaseChange B f.left).obj U)) at hq
  dsimp only [sectionMap]
  rw [← Category.assoc, hq, Category.assoc,
    ← (φ.app T').hom.naturality, ← Category.assoc]

public def reconstructionDataIso :
    𝟭 (BigEtaleSheafData.{u, v} B S hS) ≅
      reconstructedSheafFunctor B S hS ⋙ bigEtaleSheafRestriction B S hS := by
  refine NatIso.ofComponents (fun (D : BigEtaleSheafData.{u, v} B S hS) =>
    @asIso _ _ _ _ (reconstructionDataHom B S hS D)
      (dataHom_isIso_of_app B S hS _ (fun T => by
        change IsIso (reconstructedSmallIso B S hS D T).hom
        infer_instance))) ?_
  intro D E φ
  apply BigEtaleSheafData.Hom.ext
  intro T
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (φ.app T).hom.app U ≫ reconstructedSmallSectionsMap B S hS E T U.unop =
    reconstructedSmallSectionsMap B S hS D T U.unop ≫
      (φ.app _).hom.app (op (smallEtaleTerminal B S hS _))
  rw [reconstructedSmallSectionsMap_eq_sectionMap,
    reconstructedSmallSectionsMap_eq_sectionMap]
  exact sectionMap_hom_naturality B S hS φ _ _ _ _ _

public def smallTerminalToBigIso (T : BigEtaleOver B S hS) :
    (smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).obj
      (smallEtaleTerminal B S hS T) ≅ T :=
  Over.isoMk (Iso.refl _) (by
    simp [smallEtaleToBigEtaleFunctor, smallEtaleTerminal, SmallEtale.final])

public theorem reconstructedRestrictionMap
    (F : Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    reconstructedPresheafMap B S hS (restrictionData B S hS F) f =
      F.obj.map ((smallTerminalToBigIso B S hS T').hom ≫ f ≫
        (smallTerminalToBigIso B S hS T).inv).op := by
  dsimp only [reconstructedPresheafMap, dataPushforwardMap, restrictionData,
    restrictionPullbackMap]
  rw [Equiv.apply_symm_apply]
  show F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  simp only [Functor.op_map, Quiver.Hom.unop_op]
  rw [← Functor.map_comp, ← op_comp]
  apply congrArg F.obj.map
  apply congrArg Quiver.Hom.op
  apply Over.OverMorphism.ext
  have hw := (smallEtaleBaseChangeTerminalIso B S hS f).inv.hom.w
  change (smallEtaleBaseChangeTerminalIso B S hS f).inv.hom.left ≫
    pullback.snd (𝟙 T.left) f.left = 𝟙 T'.left at hw
  show (smallEtaleBaseChangeTerminalIso B S hS f).inv.hom.left ≫
    pullback.fst (𝟙 T.left) f.left = 𝟙 _ ≫ f.left ≫ 𝟙 _
  have hp : pullback.fst (𝟙 T.left) f.left =
      pullback.snd (𝟙 T.left) f.left ≫ f.left := by
    simpa using (pullback.condition (f := 𝟙 T.left) (g := f.left))
  rw [hp, ← Category.assoc, hw]
  simp only [Category.comp_id, Category.id_comp]
  exact Category.id_comp _

public def reconstructionSheafIso
    (F : Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v))) :
    F ≅ reconstructedSheaf B S hS (restrictionData B S hS F) := by
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents
    (fun T => F.obj.mapIso (smallTerminalToBigIso B S hS T.unop).op) ?_
  intro T T' f
  change F.obj.map f ≫ F.obj.map (smallTerminalToBigIso B S hS T'.unop).hom.op =
    F.obj.map (smallTerminalToBigIso B S hS T.unop).hom.op ≫
      reconstructedPresheafMap B S hS (restrictionData B S hS F) f.unop
  rw [reconstructedRestrictionMap, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg F.obj.map
  have hf : f = f.unop.op := rfl
  rw [hf, ← op_comp, ← op_comp]
  apply congrArg Quiver.Hom.op
  simp

public def reconstructionSheafNatIso :
    𝟭 (Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v))) ≅
      bigEtaleSheafRestriction B S hS ⋙ reconstructedSheafFunctor B S hS := by
  refine NatIso.ofComponents (fun F => reconstructionSheafIso B S hS F) ?_
  intro F G φ
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  exact (φ.hom.naturality (smallTerminalToBigIso B S hS T.unop).hom.op).symm

/-- **Stacks Project, Tag 021K.** A sheaf on the big étale site over `S` is precisely a
compatible family of sheaves on the small étale sites of all the schemes over `S`: the
restriction functor is an equivalence of categories. -/
@[stacks 021K "equivalence with big étale sheaves"]
public def characterizeSheafBigEtale :
    Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)) ≌
      BigEtaleSheafData.{u, v} B S hS :=
  CategoryTheory.Equivalence.mk (bigEtaleSheafRestriction B S hS)
    (reconstructedSheafFunctor B S hS) (reconstructionSheafNatIso B S hS)
    (reconstructionDataIso B S hS).symm

/-- The equivalence is the canonical restriction functor, not merely some functor. -/
public theorem characterizeSheafBigEtale_functor :
    (characterizeSheafBigEtale.{u, v} B S hS).functor = bigEtaleSheafRestriction B S hS :=
  rfl

/-- **Stacks Project, Tag 021K.** Evaluating the equivalence at a scheme `T` over `S` is
restriction to the small étale site of `T`. -/
@[stacks 021K "equivalence with big étale sheaves"]
public theorem characterizeSheafBigEtale_functor_comp_eval (T : BigEtaleOver B S hS) :
    (characterizeSheafBigEtale.{u, v} B S hS).functor ⋙ BigEtaleSheafData.eval B S hS T =
      bigEtaleSheafRestrictionAt B S hS T :=
  rfl

/-- **Stacks Project, Tag 021K.** Under the equivalence the adjoint of each comparison map is
restriction along the projection `U ×[T] T' ⟶ U`, for every small étale object `U` of `T`; so
the equivalence determines the comparison maps as well as the sheaves. -/
@[stacks 021K "equivalence with big étale sheaves"]
public theorem characterizeSheafBigEtale_pullback_app
    (F : Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)))
    {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
    (U : SmallEtale B T.left.1 T.left.property) :
    ((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _
        (((characterizeSheafBigEtale.{u, v} B S hS).functor.obj F).pullback f)).hom.app
          (op U) =
      F.obj.map (bigEtaleBaseChangeProjection B S hS f U).op := by
  show ((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _
    (((B.smallPullbackAdjunction f.left (Type (max (u + 1) v))).homEquiv _ _).symm
      (restrictionPushforwardMap B S hS F f))).hom.app (op U) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- **Stacks Project, Tag 021K.** Restriction to the small étale sites is an equivalence. -/
public instance bigEtaleSheafRestriction_isEquivalence :
    (bigEtaleSheafRestriction.{u, v} B S hS).IsEquivalence :=
  (characterizeSheafBigEtale.{u, v} B S hS).isEquivalence_functor

end AlgebraicGeometry

end
