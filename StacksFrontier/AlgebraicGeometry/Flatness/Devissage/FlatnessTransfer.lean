module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessStalkTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.ElementaryDevissage
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness

/-!
# Flatness along an elementary dévissage

Let `D` be an elementary dévissage of a finite-type quasi-coherent module `F` along `f : X ⟶ S`
at a point `x` (Stacks 057S, `AlgebraicGeometry.ElementaryDevissage`): étale neighbourhoods `U`
of `(X, x)` and `V` of `(S, f x)`, a finitely presented closed immersion `i : Z ⟶ U` carrying a
module `G` with `i_* G ≅ g^* F`, and a factorisation of `Z ⟶ V` as a finite `π : Z ⟶ Y` followed
by a smooth `h : Y ⟶ V`.

This file proves Stacks 057U: the three modules `F`, `G` and `π_* G` are flat over the base —
near their distinguished points, and on their stalks at those points — simultaneously.

## Main definitions

* `AlgebraicGeometry.IsFlatOverNear`: a sheaf of modules is flat over the base at every point of
  some open neighbourhood of a point, equivalently (by
  `AlgebraicGeometry.IsFlatOverNear.iff_mem_interior_flatLocus`) a point of the interior of the
  relative flat locus `AlgebraicGeometry.flatLocus`.

## Main results

* `AlgebraicGeometry.ElementaryDevissage.isFlatOverNear_iff_closed` and
  `AlgebraicGeometry.ElementaryDevissage.isFlatOverNear_iff_pushforward`: **Stacks 057U**, the
  equivalence of conditions (1), (2) and (3).
* `AlgebraicGeometry.ElementaryDevissage.isFlatOverAt_iff_closed` and
  `AlgebraicGeometry.ElementaryDevissage.isFlatOverAt_iff_pushforward`: **Stacks 057U**, the
  equivalence of conditions (a), (b) and (c).

## Implementation notes

The source states (1) ⇔ (2) ⇔ (3) and (a) ⇔ (b) ⇔ (c) as two three-way equivalences. Each is
recorded here as a pair of two-way equivalences through the middle condition, which is where the
proof factors: the step from `F` to `G` is étale descent of flatness (Stacks 02JZ) followed by
the closed immersion, and the step from `G` to `π_* G` is the finite morphism `π` with its
singleton fibre.

Flatness over `S` and over the étale neighbourhood `V` are interchanged throughout by Stacks
05B9, `AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale`. The comparison of a module with its
direct image along a finite morphism is Stacks 0FLM globally and Stacks 05B8 on stalks; both are
applied to the restriction of the morphism over an open of the target, which is identified with
the restriction of the direct image by
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`.

## References

* [Stacks Project, Tag 057U](https://stacks.math.columbia.edu/tag/057U)
* [Stacks Project, Tag 057S](https://stacks.math.columbia.edu/tag/057S)
* [Stacks Project, Tag 05B8](https://stacks.math.columbia.edu/tag/05B8)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A sheaf of modules is flat over the base *near* a point if it is flat over the base at every
point of some open neighbourhood of that point. -/
def IsFlatOverNear {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ ∀ y : X, y ∈ U → IsFlatOverAt f.toLRSHom.toShHom F y

/-- Mathlib's pullback of modules on schemes is the pullback of the ringed-space module
adjunction at the underlying morphism of ringed spaces. -/
private alias modulePullback_eq_pullback :=
  ElementaryEtaleFlatness.modulePullback_eq_schemePullback

/-- Flatness over the base at the image of a point under a flat morphism `e` is flatness of the
pullback along `e` at that point (Stacks 02JZ). -/
theorem isFlatOverAt_iff_pullback_isFlatOverAt {X Y S : Scheme.{u}} (e : Y ⟶ X) [Flat e]
    (f : X ⟶ S) (F : X.Modules) (z : Y) :
    IsFlatOverAt f.toLRSHom.toShHom F (e z) ↔
      IsFlatOverAt (e ≫ f).toLRSHom.toShHom ((Scheme.Modules.pullback e).obj F) z := by
  simpa only [modulePullback_eq_pullback] using
    isFlatOverAt_iff_modulePullback_isFlatOverAt e f F z
      (show IsFlatAt e.toLRSHom.toShHom z from Flat.stalkMap e z)

namespace IsFlatOverNear

/-- Flatness over the base near a point is unchanged when flatness at every point is. -/
theorem congr_of_forall_iff {X S T : Scheme.{u}} {f : X ⟶ S} {g : X ⟶ T} {F G : X.Modules}
    {x : X}
    (h : ∀ y, IsFlatOverAt f.toLRSHom.toShHom F y ↔ IsFlatOverAt g.toLRSHom.toShHom G y) :
    IsFlatOverNear f F x ↔ IsFlatOverNear g G x :=
  ⟨fun ⟨U, hxU, hU⟩ => ⟨U, hxU, fun y hy => (h y).mp (hU y hy)⟩,
   fun ⟨U, hxU, hU⟩ => ⟨U, hxU, fun y hy => (h y).mpr (hU y hy)⟩⟩

/-- Flatness over the base near a point is membership of the interior of the relative flat
locus `AlgebraicGeometry.flatLocus`. For a finite-type module the flat locus is open (Stacks
05IK), and then the two conditions are plain membership of it; Stacks 057U assumes no
finiteness, so the neighbourhood is carried in the statement. -/
theorem iff_mem_interior_flatLocus {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) :
    IsFlatOverNear f F x ↔ x ∈ interior (flatLocus f F) :=
  ⟨fun ⟨U, hxU, hU⟩ => mem_interior.mpr ⟨(U : Set X), fun y hy => hU y hy, U.isOpen, hxU⟩,
   fun hx =>
    let ⟨W, hWsub, hWopen, hxW⟩ := mem_interior.mp hx
    ⟨⟨W, hWopen⟩, hxW, fun _y hy => hWsub hy⟩⟩

/-- Flatness over the base near a point is invariant under an isomorphism of modules. -/
theorem iff_of_iso {X S : Scheme.{u}} (f : X ⟶ S) {F G : X.Modules} (e : F ≅ G) (x : X) :
    IsFlatOverNear f F x ↔ IsFlatOverNear f G x :=
  congr_of_forall_iff fun y => flatOverAt_iff_of_iso f e y

/-- Flatness over the base near a point is a statement about a neighbourhood, so it is unchanged
by restricting to an open subscheme containing the point. -/
theorem iff_restrict {W X S : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (f : X ⟶ S)
    (F : X.Modules) (w : W) :
    IsFlatOverNear f F (j w) ↔ IsFlatOverNear (j ≫ f) (F.restrict j) w := by
  constructor
  · rintro ⟨U, hxU, hU⟩
    exact ⟨j ⁻¹ᵁ U, hxU, fun y hy => (isFlatOverAt_restrict_iff j f F y).2 (hU (j y) hy)⟩
  · rintro ⟨V, hwV, hV⟩
    refine ⟨⟨j '' (V : Set W), j.isOpenMap (V : Set W) V.2⟩, ⟨w, hwV, rfl⟩, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact (isFlatOverAt_restrict_iff j f F z).mp (hV z hz)

/-- Flatness over the base near a point is flatness over the base on some open neighbourhood. -/
theorem iff_exists_isFlatOver_restrict {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) :
    IsFlatOverNear f F x ↔ ∃ U : X.Opens, x ∈ U ∧
      IsFlatOver (U.ι ≫ f).toLRSHom.toShHom (F.restrict U.ι) := by
  constructor
  · rintro ⟨U, hxU, hU⟩
    exact ⟨U, hxU, fun w => (isFlatOverAt_restrict_iff U.ι f F w).2 (hU (U.ι w) w.2)⟩
  · rintro ⟨U, hxU, hU⟩
    exact ⟨U, hxU, fun y hy => (isFlatOverAt_restrict_iff U.ι f F ⟨y, hy⟩).mp (hU ⟨y, hy⟩)⟩

/-- **Flatness over the base near a point is unchanged by an étale pullback.** An étale morphism
is flat and open, so Stacks 02JZ compares flatness over the base at a point with flatness of the
pullback at any preimage of it. -/
theorem iff_etale_pullback {X Y S : Scheme.{u}} (e : Y ⟶ X) [Etale e] (f : X ⟶ S)
    (F : X.Modules) (x : X) (y : Y) (hey : e y = x) :
    IsFlatOverNear f F x ↔
      IsFlatOverNear (e ≫ f) ((Scheme.Modules.pullback e).obj F) y := by
  constructor
  · rintro ⟨U, hxU, hU⟩
    exact ⟨e ⁻¹ᵁ U, show e y ∈ U from hey ▸ hxU,
      fun z hz => (isFlatOverAt_iff_pullback_isFlatOverAt e f F z).mp (hU (e z) hz)⟩
  · rintro ⟨U, hyU, hU⟩
    refine ⟨⟨e '' (U : Set Y), e.isOpenMap (U : Set Y) U.2⟩, ⟨y, hyU, hey⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact (isFlatOverAt_iff_pullback_isFlatOverAt e f F w).mpr (hU w hw)

/-- **Flatness over the base near a point transfers across a finite morphism with a singleton
fibre.** For `f : X ⟶ Y` finite whose fibre over `y` is `{x}` and `q : Y ⟶ S`, a quasi-coherent
module is flat over `S` near `x` exactly when its direct image is flat over `S` near `y`.

Stacks 05B8 produces a neighbourhood of `y` whose inverse image lies inside any prescribed
neighbourhood of `x`, and Stacks 0FLM compares flatness of a module over `S` with that of its
direct image along the restricted finite morphism. -/
theorem iff_pushforward_of_finite {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (q : Y ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (x : X) (y : Y) (hxy : f x = y)
    (hfiber : f ⁻¹' ({y} : Set Y) = {x}) :
    IsFlatOverNear (f ≫ q) F x ↔
      IsFlatOverNear q ((Scheme.Modules.pushforward f).obj F) y := by
  rw [iff_exists_isFlatOver_restrict (f ≫ q) F x,
    iff_exists_isFlatOver_restrict q ((Scheme.Modules.pushforward f).obj F) y]
  have hcomp (V : Y.Opens) : (f ∣_ V) ≫ V.ι ≫ q = (f ⁻¹ᵁ V).ι ≫ (f ≫ q) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have key (V : Y.Opens) :
      IsFlatOver (V.ι ≫ q).toLRSHom.toShHom (((Scheme.Modules.pushforward f).obj F).restrict V.ι) ↔
        IsFlatOver ((f ⁻¹ᵁ V).ι ≫ f ≫ q).toLRSHom.toShHom (F.restrict (f ⁻¹ᵁ V).ι) := by
    have : (F.restrict (f ⁻¹ᵁ V).ι).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor _ F
    rw [← hcomp]
    exact (isFlatOver_iff_of_iso (V.ι ≫ q)
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app F)).trans
      (isFlatOver_pushforward_iff (f ∣_ V) (V.ι ≫ q) (F.restrict (f ⁻¹ᵁ V).ι)).symm
  constructor
  · rintro ⟨U, hxU, hU⟩
    obtain ⟨V, hyV, hpre⟩ := exists_open_preimage_le f x y hxy hfiber U hxU
    exact ⟨V, hyV, (key V).mpr fun w =>
      (isFlatOverAt_restrict_iff (f ⁻¹ᵁ V).ι (f ≫ q) F w).2
        ((isFlatOverAt_restrict_iff U.ι (f ≫ q) F ⟨(f ⁻¹ᵁ V).ι w, hpre w.2⟩).mp
          (hU ⟨(f ⁻¹ᵁ V).ι w, hpre w.2⟩))⟩
  · rintro ⟨V, hyV, hV⟩
    exact ⟨f ⁻¹ᵁ V, show f x ∈ V from hxy ▸ hyV, (key V).mp hV⟩

end IsFlatOverNear

/-- **Flatness over the base at a point transfers across a finite morphism with a singleton
fibre.** For `i : X ⟶ Y` finite whose fibre over `i x` is `{x}` and `p : Y ⟶ S` with
`i ≫ p = f`, a quasi-coherent module `F` is flat over `S` at `x` exactly when its direct image
`i_* F` is flat over `S` at `i x`.

The two stalks are isomorphic as `𝒪_{Y,i x}`-modules by Stacks 05B8, and the action of
`𝒪_{S,p (i x)}` on each factors through that of `𝒪_{Y,i x}`, so the two flatness statements are
the same by `Module.Flat.equiv_iff`. -/
theorem isFlatOverAt_pushforward_iff {X Y S : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ S)
    (f : X ⟶ S) (hcomp : i ≫ p = f) [IsFinite i] (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (hfiber : i ⁻¹' ({i x} : Set Y) = {x}) :
    IsFlatOverAt f.toLRSHom.toShHom F x ↔
      IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pushforward i).obj F) (i x) := by
  obtain ⟨e⟩ := stalk_isomorphic_pushforward_of_finite_singleton_fiber i x hfiber F
  let Mx := TopCat.Presheaf.stalk F.val.presheaf x
  let My := TopCat.Presheaf.stalk ((Scheme.Modules.pushforward i).obj F).val.presheaf (i x)
  rw [← hcomp]
  let R := S.presheaf.stalk (p (i x))
  let A := Y.presheaf.stalk (i x)
  let α := (p.stalkMap (i x)).hom
  let β := (i.stalkMap x).hom
  let : Algebra R A := α.toAlgebra
  let : Module (X.presheaf.stalk x) Mx :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module A Mx := Module.compHom _ β
  let : Module (Y.presheaf.stalk (i x)) My :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) ((Scheme.Modules.pushforward i).obj F).val (i x)
  let : Module R Mx := Module.compHom _ ((i ≫ p).stalkMap x).hom
  let : Module R My := Module.compHom _ α
  have : IsScalarTower R A Mx := IsScalarTower.of_algebraMap_smul fun r z => by
    change β (α r) • z = ((i ≫ p).stalkMap x).hom r • z
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have : IsScalarTower R A My := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : LinearMap.CompatibleSMul Mx My R A := ⟨fun g r z => by
    rw [← IsScalarTower.algebraMap_smul (R := R) (A := A) (M := My) r (g z),
      ← IsScalarTower.algebraMap_smul (R := R) (A := A) (M := Mx) r z]
    exact g.map_smul _ _⟩
  change Module.Flat R Mx ↔ Module.Flat R My
  exact Module.Flat.equiv_iff (e.toLinearEquiv.restrictScalars R)

namespace ElementaryDevissage

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
  {hx : f.asFiber x ∈
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)}

/-- **Stacks Project, Tag 057U**, the equivalence of conditions (a) and (b). In an elementary
dévissage the stalk `F_x` is flat over `𝒪_{S,f x}` exactly when the stalk `G_z` is flat over
`𝒪_{V,h (π z)}`.

The étale morphism `U ⟶ X` is flat, so Stacks 02JZ replaces `F` at `x` by its pullback to `U` at
the distinguished point; Stacks 05B9 replaces flatness over `S` by flatness over `V`; the
pullback of `F` to `U` is `i_* G`; and the closed immersion `i` is finite with singleton fibre,
so Stacks 05B8 exchanges the stalk of `i_* G` for the stalk of `G`. -/
@[stacks 057U "equivalence of (a), (b) and (c)"]
theorem isFlatOverAt_iff_closed [F.IsQuasicoherent] (D : ElementaryDevissage f F x hx) :
    IsFlatOverAt f.toLRSHom.toShHom F x ↔
      IsFlatOverAt (D.π ≫ D.h).toLRSHom.toShHom D.G D.z := by
  have : IsClosedImmersion D.i := D.closedImmersion
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  have hfiber : D.i ⁻¹' ({D.i D.z} : Set D.U.scheme) = {D.z} := by
    rw [D.point_closed]
    exact D.preimage_i_singleton
  calc IsFlatOverAt f.toLRSHom.toShHom F x
      ↔ IsFlatOverAt (D.U.toBase ≫ f).toLRSHom.toShHom
          ((Scheme.Modules.pullback D.U.toBase).obj F) D.U.point := by
        simpa only [D.U.map_point] using
          isFlatOverAt_iff_pullback_isFlatOverAt D.U.toBase f F D.U.point
    _ ↔ IsFlatOverAt (D.toBase ≫ D.V.toBase).toLRSHom.toShHom
          ((Scheme.Modules.pullback D.U.toBase).obj F) D.U.point := by rw [D.commutes_base]
    _ ↔ IsFlatOverAt D.toBase.toLRSHom.toShHom
          ((Scheme.Modules.pullback D.U.toBase).obj F) D.U.point :=
        isFlatOverAt_comp_iff_of_etale D.toBase D.V.toBase
          ((Scheme.Modules.pullback D.U.toBase).obj F) D.U.point
    _ ↔ IsFlatOverAt D.toBase.toLRSHom.toShHom
          ((Scheme.Modules.pushforward D.i).obj D.G) (D.i D.z) := by
        rw [D.point_closed]
        exact (flatOverAt_iff_of_iso D.toBase D.sheafIso D.U.point).symm
    _ ↔ IsFlatOverAt (D.i ≫ D.toBase).toLRSHom.toShHom D.G D.z :=
        (isFlatOverAt_pushforward_iff D.i D.toBase (D.i ≫ D.toBase) rfl D.G D.z hfiber).symm
    _ ↔ IsFlatOverAt (D.π ≫ D.h).toLRSHom.toShHom D.G D.z := by rw [D.commutes_closed]

/-- **Stacks Project, Tag 057U**, the equivalence of conditions (b) and (c). In an elementary
dévissage the stalk `G_z` is flat over `𝒪_{V,h (π z)}` exactly when the stalk `(π_* G)_{π z}`
is.

The morphism `π` is finite and its fibre over `π z` is `{z}`, so this is the transfer of
flatness over the base at a point across a finite morphism with a singleton fibre. -/
@[stacks 057U "equivalence of (a), (b) and (c)"]
theorem isFlatOverAt_iff_pushforward (D : ElementaryDevissage f F x hx) :
    IsFlatOverAt (D.π ≫ D.h).toLRSHom.toShHom D.G D.z ↔
      IsFlatOverAt D.h.toLRSHom.toShHom
        ((Scheme.Modules.pushforward D.π).obj D.G) (D.π D.z) := by
  have : IsFinite D.π := D.finite_π
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  exact isFlatOverAt_pushforward_iff D.π D.h (D.π ≫ D.h) rfl D.G D.z D.preimage_π_singleton

/-- **Stacks Project, Tag 057U**, the equivalence of conditions (1) and (2). In an elementary
dévissage, `F` is flat over `S` near `x` exactly when `G` is flat over `V` near `z`.

The étale morphism `U ⟶ X` is flat and open, so Stacks 02JZ transfers flatness over the base
near `x` to flatness of the pullback near the distinguished point of `U`; Stacks 05B9 interchanges
flatness over `S` and over `V`; the pullback is `i_* G`; and the closed immersion `i` is finite
with singleton fibre, so Stacks 0FLM and Stacks 05B8 exchange `i_* G` and `G`. -/
@[stacks 057U "equivalence of (1), (2) and (3)"]
theorem isFlatOverNear_iff_closed [F.IsQuasicoherent] (D : ElementaryDevissage f F x hx) :
    IsFlatOverNear f F x ↔ IsFlatOverNear (D.π ≫ D.h) D.G D.z := by
  have : IsClosedImmersion D.i := D.closedImmersion
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  have hbase : IsFlatOverNear D.toBase ((Scheme.Modules.pullback D.U.toBase).obj F) D.U.point ↔
      IsFlatOverNear (D.U.toBase ≫ f) ((Scheme.Modules.pullback D.U.toBase).obj F)
        D.U.point := by
    rw [D.commutes_base]
    exact (IsFlatOverNear.congr_of_forall_iff fun y => isFlatOverAt_comp_iff_of_etale D.toBase
      D.V.toBase ((Scheme.Modules.pullback D.U.toBase).obj F) y).symm
  rw [← D.commutes_closed]
  exact (IsFlatOverNear.iff_etale_pullback D.U.toBase f F x D.U.point D.U.map_point).trans
    (hbase.symm.trans ((IsFlatOverNear.iff_of_iso D.toBase D.sheafIso D.U.point).symm.trans
      (IsFlatOverNear.iff_pushforward_of_finite D.i D.toBase D.G D.z D.U.point
        D.point_closed D.preimage_i_singleton).symm))

/-- **Stacks Project, Tag 057U**, the equivalence of conditions (2) and (3). In an elementary
dévissage, `G` is flat over `V` near `z` exactly when `π_* G` is flat over `V` near `π z`.

The morphism `π` is finite and its fibre over `π z` is `{z}`, so this is the transfer of
flatness over the base near a point across a finite morphism with a singleton fibre. -/
@[stacks 057U "equivalence of (1), (2) and (3)"]
theorem isFlatOverNear_iff_pushforward (D : ElementaryDevissage f F x hx) :
    IsFlatOverNear (D.π ≫ D.h) D.G D.z ↔
      IsFlatOverNear D.h ((Scheme.Modules.pushforward D.π).obj D.G) (D.π D.z) := by
  have : IsFinite D.π := D.finite_π
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  exact IsFlatOverNear.iff_pushforward_of_finite D.π D.h D.G D.z (D.π D.z) rfl
    D.preimage_π_singleton

end ElementaryDevissage

end AlgebraicGeometry

end
