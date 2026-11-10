module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Contraction
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk

/-!
# The direct image of the structure sheaf along a morphism of schemes

This file collects the sheaf-of-modules machinery needed to compare the structure sheaf of the
target of a morphism of schemes with the direct image of the structure sheaf of its source. It
is written for the contraction of a rational bridge, where the comparison map is an isomorphism
because the two structure sheaves are fibre products of the same two sheaves over the same base
(Tag 0E3M), but nothing here is special to that situation.

## Main definitions

* `AlgebraicGeometry.structureSheafToPushforward` is the canonical comparison map from the
  structure sheaf of the target to the direct image of the structure sheaf of the source.
* `AlgebraicGeometry.pushedForwardStructureSheaf` is its codomain, the direct image of the
  structure sheaf of the source.

## Main results

* `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_of_isIso_ringCatSheafHom` reduces
  invertibility of the canonical map of sheaves of modules to invertibility of the underlying
  map of sheaves of rings.
* `AlgebraicGeometry.isIso_toRingCatSheafHom_toSpecΓ` and
  `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_toSpecΓ` treat the canonical morphism to
  the spectrum of the global functions of a quasi-compact quasi-separated scheme: there the
  comparison map is an isomorphism, since the basic opens form a basis on which it is the
  identification of sections of the structure sheaf of a spectrum.
* `AlgebraicGeometry.structureSheafToPushforward_app`,
  `AlgebraicGeometry.structureSheafToPushforward_comp` and
  `AlgebraicGeometry.structureSheafToPushforward_congr` compute the comparison map on sections
  and record its compatibility with composition and with equal morphisms.
* `AlgebraicGeometry.isIso_structureSheafToPushforward_of_isIso` is the case of an isomorphism.
* `AlgebraicGeometry.isIso_of_isPullback_comparison`: a morphism between the vertices of two
  pullback squares compatible with isomorphisms of the other three corners is an isomorphism.
* `AlgebraicGeometry.pushforward_map_isPullback`: the direct-image functor on sheaves of modules
  preserves pullback squares.
* `AlgebraicGeometry.pushoutModuleSquare_isPullback`: if the rings of sections over every open
  of the target of a pushout square of schemes form a pullback square, then the four structure
  sheaves of modules form a pullback square. This is the step at which the contraction argument
  consumes the structure-sheaf assertion of Tag 0E25, which is supplied here as a hypothesis
  because it is not available in the library.

## Implementation notes

The canonical morphism of sheaves of modules is Mathlib's
`SheafOfModules.unitToPushforwardObjUnit` applied to
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`. Invertibility is transferred between the ring
and module levels sectionwise rather than through functoriality in the morphism of sheaves of
rings, which is not available: on sections the module map is literally the ring map pushed along
`forget₂ RingCat AddCommGrpCat`, so `CategoryTheory.NatTrans.isIso_iff_isIso_app` after
reflection along `SheafOfModules.toSheaf` and `CategoryTheory.sheafToPresheaf` reduces the claim
to the ring statement.

Invertibility of a morphism of sheaves is unpacked to its sections by hand, through
`CategoryTheory.IsIso.out`, instead of by applying a functor to an isomorphism. The reason is
that `TopCat.Sheaf` is a definition wrapping `CategoryTheory.Sheaf` and carries its own derived
category instance, so a morphism of `TopCat.Sheaf`s is not syntactically a morphism of
`CategoryTheory.Sheaf`s and instance search for `CategoryTheory.Functor.map_isIso` does not fire
on it.

The structure sheaf read as a module over itself is `AlgebraicGeometry.structureSheafModule`,
imported from `StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/StructureSheafStalk.lean`
rather than redeclared here.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- An isomorphism of sheaves of rings on a topological space is an isomorphism on the sections
over every open set. -/
theorem isIso_hom_app_of_isIso_sheafHom {Z : TopCat.{u}} {F G : TopCat.Sheaf RingCat.{u} Z}
    {φ : F ⟶ G} (h : IsIso φ) (U : (TopologicalSpace.Opens Z)ᵒᵖ) :
    IsIso (φ.hom.app U) := by
  obtain ⟨ψ, h₁, h₂⟩ := h.out
  refine ⟨⟨ψ.hom.app U, ?_, ?_⟩⟩
  · exact congrArg (fun α : F ⟶ F => α.hom.app U) h₁
  · exact congrArg (fun α : G ⟶ G => α.hom.app U) h₂

/-- If the map of sheaves of rings attached to a morphism of schemes is an isomorphism on the
sections over every open set, then the canonical map of sheaves of modules from the structure
sheaf of the target to the direct image of the structure sheaf of the source is an
isomorphism. -/
theorem isIso_unitToPushforwardObjUnit_of_forall_isIso_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U, IsIso (f.toRingCatSheafHom.hom.app U)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  intro U
  have := hf U
  exact inferInstanceAs
    (IsIso ((forget₂ RingCat AddCommGrpCat).map (f.toRingCatSheafHom.hom.app U)))

/-- Invertibility of the canonical map of sheaves of modules attached to a morphism of schemes
follows from invertibility of its map of sheaves of rings. -/
theorem isIso_unitToPushforwardObjUnit_of_isIso_ringCatSheafHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsIso f.toRingCatSheafHom) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :=
  isIso_unitToPushforwardObjUnit_of_forall_isIso_app f
    (isIso_hom_app_of_isIso_sheafHom hf)

/-- For a quasi-compact quasi-separated scheme the canonical map of sheaves of rings to the
direct image along `AlgebraicGeometry.Scheme.toSpecΓ` is an isomorphism. -/
theorem isIso_toRingCatSheafHom_toSpecΓ {Z : Scheme.{u}}
    [CompactSpace Z] [QuasiSeparatedSpace Z] :
    IsIso Z.toSpecΓ.toRingCatSheafHom := by
  let φ : (Spec Γ(Z, ⊤)).ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat Z.toSpecΓ.base).obj Z.ringCatSheaf :=
    Z.toSpecΓ.toRingCatSheafHom
  refine TopCat.Sheaf.isIso_iff_isIso_basis (φ := φ) PrimeSpectrum.isBasis_basic_opens
    fun a => ?_
  have : IsIso (Z.toSpecΓ.app (PrimeSpectrum.basicOpen a)) :=
    isIso_ΓSpec_adjunction_unit_app_basicOpen a
  change IsIso ((forget₂ CommRingCat RingCat).map
    (Z.toSpecΓ.c.app (op (PrimeSpectrum.basicOpen a))))
  infer_instance

/-- For a quasi-compact quasi-separated scheme the canonical map of sheaves of modules to the
direct image along `AlgebraicGeometry.Scheme.toSpecΓ` is an isomorphism. -/
theorem isIso_unitToPushforwardObjUnit_toSpecΓ {Z : Scheme.{u}}
    [CompactSpace Z] [QuasiSeparatedSpace Z] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit Z.toSpecΓ.toRingCatSheafHom) :=
  isIso_unitToPushforwardObjUnit_of_isIso_ringCatSheafHom Z.toSpecΓ
    isIso_toRingCatSheafHom_toSpecΓ

/-- The direct image of the structure sheaf of the source along a morphism of schemes. -/
abbrev pushedForwardStructureSheaf {X P : Scheme.{u}} (f : X ⟶ P) : P.Modules :=
  (Scheme.Modules.pushforward f).obj (structureSheafModule X)

/-- The canonical map from the structure sheaf of the target of a morphism of schemes to the
direct image of the structure sheaf of its source. -/
def structureSheafToPushforward {X P : Scheme.{u}} (f : X ⟶ P) :
    structureSheafModule P ⟶ pushedForwardStructureSheaf f :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- On sections the canonical comparison map is the map on sections of the morphism of schemes,
pushed along the forgetful functor to abelian groups. -/
theorem structureSheafToPushforward_app {X P : Scheme.{u}} (f : X ⟶ P) (U : P.Opens) :
    (structureSheafToPushforward f).app U =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map (f.app U) := by
  ext x
  rfl

/-- The canonical comparison map of a composite is the composite of the comparison maps. -/
theorem structureSheafToPushforward_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSheafToPushforward (f ≫ g) =
      structureSheafToPushforward g ≫
        (Scheme.Modules.pushforward g).map (structureSheafToPushforward f) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (structureSheafModule X) := by
  ext U x
  rfl

/-- The canonical comparison map of an isomorphism of schemes is an isomorphism. -/
theorem isIso_structureSheafToPushforward_of_isIso {Z X : Scheme.{u}} (e : Z ⟶ X) [IsIso e] :
    IsIso (structureSheafToPushforward e) := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U => ?_
  change IsIso ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map (e.app U))
  infer_instance

/-- A morphism between the vertices of two pullback squares which is compatible with
isomorphisms of the other three corners is itself an isomorphism. -/
theorem isIso_of_isPullback_comparison {C : Type*} [Category C]
    {P Q A A' B B' D D' : C}
    {f : P ⟶ A} {g : P ⟶ B} {h : A ⟶ D} {k : B ⟶ D}
    {f' : Q ⟶ A'} {g' : Q ⟶ B'} {h' : A' ⟶ D'} {k' : B' ⟶ D'}
    (hp : IsPullback f g h k) (hq : IsPullback f' g' h' k')
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D')
    (hA : eA.hom ≫ h' = h ≫ eD.hom) (hB : eB.hom ≫ k' = k ≫ eD.hom)
    (m : P ⟶ Q) (hmA : m ≫ f' = f ≫ eA.hom) (hmB : m ≫ g' = g ≫ eB.hom) : IsIso m := by
  have hA' : eA.inv ≫ h = h' ≫ eD.inv := by
    simpa using (congrArg (fun t => eA.inv ≫ t ≫ eD.inv) hA).symm
  have hB' : eB.inv ≫ k = k' ≫ eD.inv := by
    simpa using (congrArg (fun t => eB.inv ≫ t ≫ eD.inv) hB).symm
  have hw : (f' ≫ eA.inv) ≫ h = (g' ≫ eB.inv) ≫ k := by
    simp only [Category.assoc, hA', hB', reassoc_of% hq.w]
  refine ⟨⟨hp.lift (f' ≫ eA.inv) (g' ≫ eB.inv) hw, hp.hom_ext ?_ ?_, hq.hom_ext ?_ ?_⟩⟩ <;>
    simp [hmA, hmB, reassoc_of% hmA, reassoc_of% hmB]

/-- The direct-image functor on sheaves of modules preserves pullback squares, being a right
adjoint. -/
theorem pushforward_map_isPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P A B D : X.Modules} {pA : P ⟶ A} {pB : P ⟶ B} {qA : A ⟶ D} {qB : B ⟶ D}
    (hp : IsPullback pA pB qA qB) :
    IsPullback ((Scheme.Modules.pushforward f).map pA)
      ((Scheme.Modules.pushforward f).map pB)
      ((Scheme.Modules.pushforward f).map qA)
      ((Scheme.Modules.pushforward f).map qB) := by
  have : Limits.PreservesLimit (Limits.cospan qA qB)
      (Scheme.Modules.pushforward f) :=
    (Adjunction.rightAdjoint_preservesLimits
      (Scheme.Modules.pullbackPushforwardAdjunction f)).preservesLimitsOfShape.preservesLimit
  exact Functor.map_isPullback (Scheme.Modules.pushforward f) hp

/-- The comparison map from the direct image along a morphism to the direct image along its
precomposition with a further morphism. -/
def pushedForwardStructureSheafToComposite {Z X P : Scheme.{u}} (i : Z ⟶ X) (a : X ⟶ P) :
    pushedForwardStructureSheaf a ⟶ pushedForwardStructureSheaf (i ≫ a) :=
  (Scheme.Modules.pushforward a).map (structureSheafToPushforward i) ≫
    (Scheme.Modules.pushforwardComp i a).hom.app _

/-- On sections the comparison map to the direct image along a composite is the map on sections
of the first morphism, pushed along the forgetful functor to abelian groups. -/
theorem pushedForwardStructureSheafToComposite_app {Z X P : Scheme.{u}} (i : Z ⟶ X)
    (a : X ⟶ P) (U : P.Opens) :
    (pushedForwardStructureSheafToComposite i a).app U =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map (i.app (a ⁻¹ᵁ U)) := by
  ext x
  rfl

/-- On sections the comparison map to the direct image along a composite, followed by the
identification of the direct images along equal morphisms, is the map on sections of the first
morphism followed by the transport along the equality of opens. -/
theorem pushedForwardStructureSheafToComposite_comp_pushforwardCongr_app {Z Y P : Scheme.{u}}
    (j : Z ⟶ Y) (b : Y ⟶ P) {g : Z ⟶ P} (hg : g = j ≫ b) (U : P.Opens) :
    (pushedForwardStructureSheafToComposite j b ≫
        (Scheme.Modules.pushforwardCongr hg.symm).hom.app (structureSheafModule Z)).app U =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map (j.app (b ⁻¹ᵁ U)) ≫
        eqToHom (by subst hg; rfl) := by
  subst hg
  rw [Scheme.Modules.Hom.comp_app, pushedForwardStructureSheafToComposite_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  congr 1
  change (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
    (Z.presheaf.map (eqToHom _).op) = _
  simp only [eqToHom_op, eqToHom_map]
  rfl

/-- If the sections of the structure sheaf over every open of the target of a pushout square of
schemes form a pullback square of rings, then the four comparison maps of structure sheaves of
modules form a pullback square.

The hypothesis `hsec` is the structure-sheaf assertion of Tag 0E25 for the square `h`: for a
pushout of a closed immersion along an integral morphism whose map out of `X` is affine, the
ring of sections over an open of the pushout is the fibre product of the rings of sections on
the two sides over the ring of sections on the intersection. -/
theorem pushoutModuleSquare_isPullback
    {Z X Y P : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (a : X ⟶ P) (b : Y ⟶ P)
    (h : IsPushout i j a b)
    (hsec : ∀ U : P.Opens,
      letI e : i ⁻¹ᵁ (a ⁻¹ᵁ U) = j ⁻¹ᵁ (b ⁻¹ᵁ U) :=
        congrArg (fun f : Z ⟶ P ↦ f ⁻¹ᵁ U) h.w
      IsPullback (b.app U) (a.app U) (j.app (b ⁻¹ᵁ U))
        (i.app (a ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) e))) :
    IsPullback
      (structureSheafToPushforward a)
      (structureSheafToPushforward b)
      (pushedForwardStructureSheafToComposite i a)
      (pushedForwardStructureSheafToComposite j b ≫
        (Scheme.Modules.pushforwardCongr h.w.symm).hom.app _) := by
  let F := Scheme.Modules.toPresheaf P
  have hF : IsPullback
      (F.map (structureSheafToPushforward a))
      (F.map (structureSheafToPushforward b))
      (F.map (pushedForwardStructureSheafToComposite i a))
      (F.map (pushedForwardStructureSheafToComposite j b ≫
        (Scheme.Modules.pushforwardCongr h.w.symm).hom.app _)) := by
    refine IsPullback.of_forall_isPullback_app fun U => ?_
    let G := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    have hU' := ((hsec U.unop).map G).flip
    let e : i ⁻¹ᵁ (a ⁻¹ᵁ U.unop) = j ⁻¹ᵁ (b ⁻¹ᵁ U.unop) := by
      simpa only [Scheme.Hom.comp_preimage] using
        congrArg (fun f : Z ⟶ P ↦ f ⁻¹ᵁ U.unop) h.w
    let eR := congrArg (fun V : Z.Opens ↦ Γ(Z, V)) e.symm
    let eΓ := congrArg G.obj eR
    have htransport : G.map
        (eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) e)) = eqToHom eΓ.symm := by
      simp only [eqToHom_map]
    change IsPullback
      ((F.map (structureSheafToPushforward a)).app (op U.unop))
      ((F.map (structureSheafToPushforward b)).app (op U.unop))
      ((F.map (pushedForwardStructureSheafToComposite i a)).app (op U.unop))
      ((F.map (pushedForwardStructureSheafToComposite j b ≫
        (Scheme.Modules.pushforwardCongr h.w.symm).hom.app _)).app (op U.unop))
    have h₁ : ((F.map (structureSheafToPushforward a)).app (op U.unop)) =
        G.map (a.app U.unop) := rfl
    have h₂ : ((F.map (structureSheafToPushforward b)).app (op U.unop)) =
        G.map (b.app U.unop) := rfl
    have h₃ : ((F.map (pushedForwardStructureSheafToComposite i a)).app
        (op U.unop)) = G.map (i.app (a ⁻¹ᵁ U.unop)) :=
      pushedForwardStructureSheafToComposite_app i a U.unop
    have h₄ : ((F.map (pushedForwardStructureSheafToComposite j b ≫
        (Scheme.Modules.pushforwardCongr h.w.symm).hom.app _)).app (op U.unop)) =
        G.map (j.app (b ⁻¹ᵁ U.unop)) ≫ eqToHom eΓ :=
      pushedForwardStructureSheafToComposite_comp_pushforwardCongr_app j b h.w U.unop
    have hU'' : IsPullback (G.map (a.app U.unop)) (G.map (b.app U.unop))
        (G.map (i.app (a ⁻¹ᵁ U.unop))) (G.map (j.app (b ⁻¹ᵁ U.unop)) ≫ eqToHom eΓ) :=
      hU'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (eqToIso eΓ) rfl rfl
        (by
          change (G.map (i.app (a ⁻¹ᵁ U.unop)) ≫
            G.map (eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) e))) ≫
              eqToHom eΓ = G.map (i.app _)
          rw [htransport]
          simp)
        (by simp [G])
    rwa [h₁, h₂, h₃, h₄]
  exact hF.of_map_of_faithful F

/-- Equal morphisms of schemes have comparison maps differing by the canonical identification
of their direct-image functors. -/
theorem structureSheafToPushforward_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    structureSheafToPushforward g = structureSheafToPushforward f ≫
      (Scheme.Modules.pushforwardCongr h).hom.app (structureSheafModule X) := by
  cases h
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  have hid : ∀ h' : f = f, ((Scheme.Modules.pushforwardCongr h').hom.app
      (structureSheafModule X)).app U = 𝟙 Γ(pushedForwardStructureSheaf f, U) :=
    fun _ => by simp
  rw [Scheme.Modules.Hom.comp_app, hid, Category.comp_id]

/-- Restriction maps of a sheaf of modules along two inclusions of the same pair of opens
agree, there being only one such inclusion. -/
theorem modulePresheaf_map_eq_of_subsingleton {P : Scheme.{u}} {M : P.Modules}
    {U V : P.Opens} (f g : U ⟶ V) : M.presheaf.map f.op = M.presheaf.map g.op := by
  congr 1
  exact Subsingleton.elim _ _

/-- In the situation of a contraction, the two routes around the composite square from the
intersection to the target agree. -/
theorem pushout_composite_morphism_eq {Z X W C T Y : Scheme.{u}}
    (i : Z ⟶ X) (j : Z ⟶ C) (a₀ : X ⟶ W) (b₀ : C ⟶ W)
    (c' : W ⟶ Y) (t : C ⟶ T) (b : T ⟶ Y) (a : X ⟶ Y)
    (hpush : IsPushout i j a₀ b₀) (hp : IsPushout i (j ≫ t) a b)
    (hqd : i ≫ a = (i ≫ a₀) ≫ c') :
    j ≫ b₀ ≫ c' = j ≫ t ≫ b := by
  calc
    j ≫ b₀ ≫ c' = (i ≫ a₀) ≫ c' :=
      congrArg (fun f : Z ⟶ W => f ≫ c') hpush.w.symm
    _ = i ≫ a := hqd.symm
    _ = (j ≫ t) ≫ b := hp.w
    _ = j ≫ t ≫ b := by simp [Category.assoc]

section NonVacuity

/-- Non-vacuity of `AlgebraicGeometry.pushoutModuleSquare_isPullback`: its two hypotheses are
jointly satisfiable at a square that is not the identity square. For an arbitrary morphism of
schemes `f : X ⟶ Y`, the square with legs `𝟙 X` and `f` into `Y` is a pushout, and the
structure-sheaf hypothesis holds on it because both of its ring squares have an identity leg. -/
theorem pushoutModuleSquare_isPullback_nonvacuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsPullback (structureSheafToPushforward f) (structureSheafToPushforward (𝟙 Y))
      (pushedForwardStructureSheafToComposite (𝟙 X) f)
      (pushedForwardStructureSheafToComposite f (𝟙 Y) ≫
        (Scheme.Modules.pushforwardCongr
          (IsPushout.of_id_fst (f := f)).w.symm).hom.app _) := by
  refine pushoutModuleSquare_isPullback (𝟙 X) f f (𝟙 Y) IsPushout.of_id_fst ?_
  intro U
  simp only [Scheme.Hom.id_app]
  exact IsPullback.of_id_fst

/-- Non-vacuity of `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_toSpecΓ`: its two instance
hypotheses resolve at a concrete scheme, so the statement has an inhabited instance. -/
theorem isIso_unitToPushforwardObjUnit_toSpecΓ_nonvacuous :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
      (Spec (CommRingCat.of ℤ)).toSpecΓ.toRingCatSheafHom) :=
  isIso_unitToPushforwardObjUnit_toSpecΓ

/-- Non-vacuity of `AlgebraicGeometry.isIso_of_isPullback_comparison`: its nine hypotheses are
jointly satisfiable, at the comparison of a pullback square with itself. -/
theorem isIso_of_isPullback_comparison_nonvacuous {C : Type*} [Category C] {A B D : C}
    {h : A ⟶ D} {k : B ⟶ D} {P : C} {f : P ⟶ A} {g : P ⟶ B} (hp : IsPullback f g h k) :
    IsIso (𝟙 P) :=
  isIso_of_isPullback_comparison hp hp (Iso.refl A) (Iso.refl B) (Iso.refl D)
    (by simp) (by simp) (𝟙 P) (by simp) (by simp)

end NonVacuity

end AlgebraicGeometry
