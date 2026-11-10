module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Pullback.OpenImmersionPushforwardStalk

/-!
# The stalk of `j_*𝒪_U` as an `𝒪_{X, x}`-module

For an open subscheme `j : U ⟶ X` of a scheme `X` and a point `x` of `X`, the direct image
`j_*𝒪_U` carries two descriptions of its stalk at `x`:

* `AlgebraicGeometry.Scheme.Hom.pushforwardStalk`, the stalk of the direct image of the
  *structure sheaf*, a commutative ring and an `𝒪_{X, x}`-algebra through
  `AlgebraicGeometry.Scheme.Hom.pushforwardStalkMap`;
* the stalk of the underlying presheaf of abelian groups of the `𝒪_X`-*module*
  `(Scheme.Modules.pushforward j).obj (SheafOfModules.unit 𝒪_U)`, an `𝒪_{X, x}`-module through
  `AlgebraicGeometry.Scheme.Modules.moduleStalk`.

This file identifies the two **as `𝒪_{X, x}`-modules** and transports the ring isomorphism
`(j_*𝒪_U)_x ≅ Γ(U_x, 𝒪_{U_x})` of
`StacksFrontier/AlgebraicGeometry/Pullback/OpenImmersionPushforwardStalk.lean` across that
identification, obtaining an `𝒪_{X, x}`-**linear** equivalence out of the module stalk which
carries the germ of the unit section to `1`.

## Why both spellings occur

The stalk of a sheaf of modules over the local ring is the input of the colimit machinery of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ModulesStalkSequenceColimit.lean` — a filtered
colimit of `𝒪_{X, x}`-modules is detected by joint surjectivity and eventual vanishing — while
the ring-theoretic identification of `(j_*𝒪_U)_x` with the sections over the inverse image of
`U` in `Spec 𝒪_{X, x}` is a statement about localizations and therefore lives in `CommRingCat`.
Neither spelling can be dispensed with, and typeclass resolution does not cross between them:
the underlying presheaf of abelian groups of the pushed-forward unit module is the composite of
the pushed-forward sheaf of rings with `forget₂ CommRingCat RingCat ⋙ forget₂ RingCat
AddCommGrpCat`, which is a definitional identity but not one instance search performs.

## The identification

Both forgetful functors preserve filtered colimits and a stalk is a filtered colimit, so
`CategoryTheory.Limits.preservesColimitIso` for their composite *is* the comparison; this is the
same step as in `Stacks.AlgebraPullbackQcoh.unitAbStalkIso` and
`Stacks.Modules.LocallyFreeRank.unitStalkLEquiv`, neither of which applies here because both are
about the unit module over the *same* sheaf of rings, whereas the module here is the unit module
of `j_*𝒪_U` restricted along the comorphism of `j`.

Scalar compatibility is the germ characterisation on both sides: a section `r` of `𝒪_X` over `V`
acts on a section of `(j_*𝒪_U)(V) = 𝒪_U(j⁻¹V)` as multiplication by `j^♯_V(r)`, by the
definition of `CategoryTheory.PresheafOfModules.pushforward`, and
`TopCat.Presheaf.stalkFunctor_map_germ` says the germ of `j^♯_V(r)` is the image
of the germ of `r` under `pushforwardStalkMap`.

## Main definitions

* `AlgebraicGeometry.pushforwardUnitStalkAddEquiv`: the comparison of the two stalks, as an
  isomorphism of additive groups.
* `AlgebraicGeometry.pushforwardUnitStalkLinearEquiv`: **the comparison as an `𝒪_{X, x}`-linear
  equivalence.**

## Main results

* `AlgebraicGeometry.pushforwardUnitStalkAddEquiv_germ`: the comparison carries a germ to the
  germ of the same section.
* `AlgebraicGeometry.pushforwardUnitStalkAddEquiv_smul`: the two scalar actions agree.
* `AlgebraicGeometry.exists_linearEquiv_pushforwardUnitStalk_of_quasiCompact`: **for a
  quasi-compact open subscheme, an `𝒪_{X, x}`-linear equivalence from the module stalk of
  `j_*𝒪_U` at `x` onto `Γ(U_x, 𝒪_{U_x})` carrying the germ of the unit section to `1`.**

This module carries no Stacks tag: as with
`StacksFrontier/AlgebraicGeometry/Pullback/OpenImmersionPushforwardStalk.lean`, the identification
is not the content of a numbered result of the Stacks Project.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (U : X.Opens) (x : X)

/-- `j_*𝒪_U` as an `𝒪_X`-module, for `j : U ⟶ X` the inclusion of an open subscheme.  This is
the vertex of the cocone of [Stacks, Tag 0EBN]. -/
abbrev pushforwardUnit : X.Modules :=
  (Scheme.Modules.pushforward U.ι).obj (SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- The stalk at `x` of the underlying presheaf of abelian groups of `j_*𝒪_U`, an
`𝒪_{X, x}`-module by `AlgebraicGeometry.Scheme.Modules.moduleStalk`. -/
abbrev pushforwardUnitStalk : Type u :=
  ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (pushforwardUnit U).val.presheaf x)

/-- The germ map of the underlying presheaf of abelian groups of `j_*𝒪_U`. -/
abbrev pushforwardUnitGerm (V : X.Opens) (hx : x ∈ V) :
    (pushforwardUnit U).val.presheaf.obj (op V) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (pushforwardUnit U).val.presheaf x :=
  TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (pushforwardUnit U).val.presheaf V x hx

/-- **The two stalks of `j_*𝒪_U` at `x` are the same additive group.**  The forgetful functors
`CommRingCat ⥤ RingCat` and `RingCat ⥤ AddCommGrpCat` preserve filtered colimits and a stalk is
a filtered colimit, so the comparison isomorphism of
`CategoryTheory.Limits.preservesColimitIso` for their composite, applied to the diagram of
neighbourhoods of `x` in the pushed-forward structure sheaf, is the identification. -/
def pushforwardUnitStalkAddEquiv :
    pushforwardUnitStalk U x ≃+ ↑(U.ι.pushforwardStalk x) :=
  (preservesColimitIso
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙
        (U.ι.base _* U.toScheme.presheaf))).symm.addCommGroupIsoToAddEquiv

/-- The inverse of the comparison carries the germ of a section of `𝒪_U` over `j⁻¹V` in the ring
`(j_*𝒪_U)_x` to the germ of the same section in the module stalk.  This is
`CategoryTheory.Limits.ι_preservesColimitIso_hom`, the germ maps being the colimit
inclusions. -/
lemma pushforwardUnitStalkAddEquiv_symm_pushforwardGerm (V : X.Opens) (hx : x ∈ V)
    (m : Γ(U.toScheme, U.ι ⁻¹ᵁ V)) :
    (pushforwardUnitStalkAddEquiv U x).symm ((U.ι.pushforwardGerm V x hx).hom m) =
      (pushforwardUnitGerm U x V hx).hom m :=
  ConcreteCategory.congr_hom
    (ι_preservesColimitIso_hom
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ (U.ι.base _* U.toScheme.presheaf)) (op ⟨V, hx⟩)) m

/-- **The comparison carries a germ to the germ of the same section.** -/
lemma pushforwardUnitStalkAddEquiv_germ (V : X.Opens) (hx : x ∈ V)
    (m : Γ(U.toScheme, U.ι ⁻¹ᵁ V)) :
    pushforwardUnitStalkAddEquiv U x ((pushforwardUnitGerm U x V hx).hom m) =
      (U.ι.pushforwardGerm V x hx).hom m :=
  (congrArg (pushforwardUnitStalkAddEquiv U x)
        (pushforwardUnitStalkAddEquiv_symm_pushforwardGerm U x V hx m)).symm.trans
    ((pushforwardUnitStalkAddEquiv U x).apply_symm_apply _)

/-- The scalar action on the sections of `j_*𝒪_U` is multiplication by the comorphism of `j`:
a section `r` of `𝒪_X` over `V` acts on `(j_*𝒪_U)(V) = 𝒪_U(j⁻¹V)` as `j^♯_V(r)` does.  This is
the definition of `CategoryTheory.PresheafOfModules.pushforward`, which is restriction of
scalars along the comorphism.  The multiplication is written out with its instance because the
two sides are stated at the two definitionally equal spellings of the same type, between which
the binary-operation elaborator does not travel. -/
lemma smul_pushforwardUnit_eq (V : X.Opens) (r : Γ(X, V))
    (m : Γ(pushforwardUnit U, V)) :
    r • m = @HMul.hMul ↑Γ(U.toScheme, U.ι ⁻¹ᵁ V) ↑Γ(U.toScheme, U.ι ⁻¹ᵁ V)
      ↑Γ(U.toScheme, U.ι ⁻¹ᵁ V) instHMul ((U.ι.app V).hom r) m := rfl

/-- The scalar and the section bound, so that the germ lemmas apply to explicit arguments.  See
`AlgebraicGeometry.pushforwardUnitStalkAddEquiv_smul`. -/
lemma pushforwardUnitStalkAddEquiv_germ_smul (V : X.Opens) (hx : x ∈ V) (r : Γ(X, V))
    (m : Γ(pushforwardUnit U, V)) :
    pushforwardUnitStalkAddEquiv U x
        ((X.presheaf.germ V x hx).hom r • (pushforwardUnitGerm U x V hx).hom m) =
      (U.ι.pushforwardStalkMap x).hom ((X.presheaf.germ V x hx).hom r) *
        pushforwardUnitStalkAddEquiv U x ((pushforwardUnitGerm U x V hx).hom m) := by
  have hsmul : (pushforwardUnitGerm U x V hx).hom (r • m) =
      (X.presheaf.germ V x hx).hom r • (pushforwardUnitGerm U x V hx).hom m :=
    Stacks.ModuleSkyscraper.germ_smul' (pushforwardUnit U).val x V hx r m
  have hgerm : (U.ι.pushforwardGerm V x hx).hom ((U.ι.app V).hom r) =
      (U.ι.pushforwardStalkMap x).hom ((X.presheaf.germ V x hx).hom r) :=
    (ConcreteCategory.congr_hom (TopCat.Presheaf.stalkFunctor_map_germ V x hx U.ι.c) r).symm
  refine Eq.trans (congrArg (pushforwardUnitStalkAddEquiv U x) hsmul.symm) ?_
  refine Eq.trans (pushforwardUnitStalkAddEquiv_germ U x V hx (r • m)) ?_
  refine Eq.trans (congrArg (U.ι.pushforwardGerm V x hx).hom
    (smul_pushforwardUnit_eq U V r m)) ?_
  refine Eq.trans (map_mul (U.ι.pushforwardGerm V x hx).hom ((U.ι.app V).hom r) m) ?_
  refine Eq.trans (congrArg (fun z => z * (U.ι.pushforwardGerm V x hx).hom m) hgerm) ?_
  exact congrArg
    (fun z => (U.ι.pushforwardStalkMap x).hom ((X.presheaf.germ V x hx).hom r) * z)
    (pushforwardUnitStalkAddEquiv_germ U x V hx m).symm

/-- **The two scalar actions agree.**  The action of `r : 𝒪_{X, x}` on the module stalk
corresponds, under the comparison, to multiplication by the image of `r` in the ring
`(j_*𝒪_U)_x`.

Both sides are pinned by their effect on germs.  Refining `r` and the element of the stalk to a
common neighbourhood of `x`, the left side is the germ of `j^♯(r) · m` by
`Stacks.ModuleSkyscraper.germ_smul'` and `smul_pushforwardUnit_eq`, and the right side is the
same because the germ map into `(j_*𝒪_U)_x` is a ring homomorphism and
`TopCat.Presheaf.stalkFunctor_map_germ` identifies the germ of `j^♯(r)` with the
image of the germ of `r`. -/
lemma pushforwardUnitStalkAddEquiv_smul (r : ↑(X.presheaf.stalk x))
    (m : pushforwardUnitStalk U x) :
    pushforwardUnitStalkAddEquiv U x (r • m) =
      (U.ι.pushforwardStalkMap x).hom r * pushforwardUnitStalkAddEquiv U x m := by
  obtain ⟨V, hxV, m₀, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (pushforwardUnit U).val.presheaf m
  obtain ⟨W, hxW, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  have hxZ : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have hm : (pushforwardUnitGerm U x (V ⊓ W) hxZ).hom
        (((pushforwardUnit U).val.presheaf.map
          (homOfLE (inf_le_left (a := V) (b := W))).op).hom m₀) =
      (pushforwardUnitGerm U x V hxV).hom m₀ :=
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) (pushforwardUnit U).val.presheaf
      (homOfLE inf_le_left) x hxZ m₀
  have hr : (X.presheaf.germ (V ⊓ W) x hxZ).hom
        ((X.presheaf.map (homOfLE (inf_le_right (a := V) (b := W))).op).hom r₀) =
      (X.presheaf.germ W x hxW).hom r₀ :=
    X.presheaf.germ_res_apply (homOfLE inf_le_right) x hxZ r₀
  rw [← hm, ← hr]
  exact pushforwardUnitStalkAddEquiv_germ_smul U x (V ⊓ W) hxZ _ _

/-- **The comparison as an `𝒪_{X, x}`-linear equivalence**, by
`AlgebraicGeometry.pushforwardUnitStalkAddEquiv_smul`: the `𝒪_{X, x}`-algebra structure on
`(j_*𝒪_U)_x` is given by `pushforwardStalkMap`, so multiplication by the image of `r` *is* the
action of `r`. -/
def pushforwardUnitStalkLinearEquiv :
    pushforwardUnitStalk U x ≃ₗ[↑(X.presheaf.stalk x)] ↑(U.ι.pushforwardStalk x) :=
  AddEquiv.toLinearEquiv (pushforwardUnitStalkAddEquiv U x) fun r m =>
    (pushforwardUnitStalkAddEquiv_smul U x r m).trans
      (Algebra.smul_def r (pushforwardUnitStalkAddEquiv U x m)).symm

/-- `pushforwardUnitStalkLinearEquiv` acts as `pushforwardUnitStalkAddEquiv`. -/
@[simp]
lemma pushforwardUnitStalkLinearEquiv_apply (m : pushforwardUnitStalk U x) :
    pushforwardUnitStalkLinearEquiv U x m = pushforwardUnitStalkAddEquiv U x m := rfl

/-- The germ of the unit section of `𝒪_U` over all of `U` goes to `1`. -/
lemma pushforwardUnitStalkLinearEquiv_one :
    pushforwardUnitStalkLinearEquiv U x
        ((pushforwardUnitGerm U x ⊤ trivial).hom
          (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ (⊤ : X.Opens)))) = 1 :=
  (pushforwardUnitStalkAddEquiv_germ U x ⊤ trivial 1).trans
    (map_one (U.ι.pushforwardGerm ⊤ x trivial).hom)

/-! ### The linear form of the identification `(j_*𝒪_U)_x ≅ Γ(U_x, 𝒪_{U_x})` -/

/-- **A ring isomorphism out of `(j_*𝒪_U)_x` that respects the two maps from `𝒪_{X, x}` is
`𝒪_{X, x}`-linear.**  The `𝒪_{X, x}`-algebra structure on `(j_*𝒪_U)_x` is `pushforwardStalkMap`
by `AlgebraicGeometry.Scheme.Hom.algebraMap_pushforwardStalk`, so `her` says exactly that the
isomorphism is a morphism of `𝒪_{X, x}`-algebras, and the action of `r` is multiplication by its
image on both sides. -/
def pushforwardStalkLinearEquivOfRingEquiv {A : Type u} [CommRing A]
    [Algebra ↑(X.presheaf.stalk x) A] (er : ↑(U.ι.pushforwardStalk x) ≃+* A)
    (her : ∀ r : ↑(X.presheaf.stalk x),
      er ((U.ι.pushforwardStalkMap x).hom r) = algebraMap ↑(X.presheaf.stalk x) A r) :
    ↑(U.ι.pushforwardStalk x) ≃ₗ[↑(X.presheaf.stalk x)] A where
  __ := er.toAddEquiv
  map_smul' r z := by
    change er (r • z) = r • er z
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (fun y => y * er z) (her r)

/-- **`(j_*𝒪_U)_x ≅ Γ(U_x, 𝒪_{U_x})` as an `𝒪_{X, x}`-linear equivalence out of the module
stalk.**

Here `U_x` is the inverse image of `U` under the canonical `f_x : Spec 𝒪_{X, x} ⟶ X`; the point
`x` need not lie in `U`.  The hypothesis on `W` is the one of
`AlgebraicGeometry.exists_ringEquiv_pushforwardStalk_ι`, that `j` be quasi-compact near `x`; it
cannot be dropped, see the module docstring there.  The hypothesis `halg` says that the
`𝒪_{X, x}`-algebra structure on the right-hand side is the canonical one, restriction along
`f_x`; it is a hypothesis rather than an instance because the algebra structure on a ring of
sections is not canonical in the typeclass system.

The equivalence is `AlgebraicGeometry.pushforwardUnitStalkLinearEquiv` followed by the ring
isomorphism of `AlgebraicGeometry.exists_ringEquiv_pushforwardStalk_ι`.  That isomorphism is
`𝒪_{X, x}`-linear by `AlgebraicGeometry.pushforwardStalkLinearEquivOfRingEquiv`, because its
defining property is exactly that it carries the canonical map from `𝒪_{X, x}` on the left to
the canonical map on the right, which `halg` identifies with the algebra map; so no
compatibility beyond that statement is needed. -/
theorem exists_linearEquiv_pushforwardUnitStalk (U : X.Opens) (x : X) {W : X.Opens}
    (hW : IsAffineOpen W) (hxW : x ∈ W)
    (hcpt : IsCompact ((U.ι ⁻¹ᵁ W : (U.toScheme).Opens) : Set U.toScheme))
    [Algebra ↑(X.presheaf.stalk x)
      ↑Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U)]
    (halg : algebraMap ↑(X.presheaf.stalk x)
        ↑Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U) =
      ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
        (Spec (X.presheaf.stalk x)).presheaf.map
          (homOfLE (le_top (a := X.fromSpecStalk x ⁻¹ᵁ U))).op).hom) :
    ∃ e : pushforwardUnitStalk U x ≃ₗ[↑(X.presheaf.stalk x)]
        ↑Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U),
      e ((pushforwardUnitGerm U x ⊤ trivial).hom
        (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ (⊤ : X.Opens)))) = 1 := by
  obtain ⟨er, her⟩ := exists_ringEquiv_pushforwardStalk_ι U x hW hxW hcpt
  refine ⟨(pushforwardUnitStalkLinearEquiv U x).trans
    (pushforwardStalkLinearEquivOfRingEquiv U x er fun r => (her r).trans ?_), ?_⟩
  · exact congrArg (fun φ : ↑(X.presheaf.stalk x) →+* _ => φ r) halg.symm
  · change er (pushforwardUnitStalkLinearEquiv U x _) = 1
    rw [pushforwardUnitStalkLinearEquiv_one]
    exact map_one er

/-- **`(j_*𝒪_U)_x ≅ Γ(U_x, 𝒪_{U_x})` as an `𝒪_{X, x}`-linear equivalence out of the module
stalk, for a quasi-compact open subscheme.**  This is
`AlgebraicGeometry.exists_linearEquiv_pushforwardUnitStalk` with the affine open neighbourhood of
`x` chosen from the basis of affine opens, as in
`AlgebraicGeometry.exists_ringEquiv_pushforwardStalk_ι_of_quasiCompact`. -/
theorem exists_linearEquiv_pushforwardUnitStalk_of_quasiCompact (U : X.Opens) [QuasiCompact U.ι]
    (x : X) [Algebra ↑(X.presheaf.stalk x)
      ↑Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U)]
    (halg : algebraMap ↑(X.presheaf.stalk x)
        ↑Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U) =
      ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
        (Spec (X.presheaf.stalk x)).presheaf.map
          (homOfLE (le_top (a := X.fromSpecStalk x ⁻¹ᵁ U))).op).hom) :
    ∃ e : pushforwardUnitStalk U x ≃ₗ[↑(X.presheaf.stalk x)]
        ↑Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U),
      e ((pushforwardUnitGerm U x ⊤ trivial).hom
        (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ (⊤ : X.Opens)))) = 1 := by
  obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact exists_linearEquiv_pushforwardUnitStalk U x hW hxW
    (U.ι.isCompact_preimage hW.isCompact) halg

end AlgebraicGeometry

end
