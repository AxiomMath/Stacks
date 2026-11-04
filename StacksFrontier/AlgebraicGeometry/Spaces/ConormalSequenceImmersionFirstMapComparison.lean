module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceClosedImmersionExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationBothEnds
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleComparison

/-!
# The first arrow of the conormal sequence across an étale change of ambient space

Let `i₀ : Z ⟶ Amb` be a morphism of algebraic spaces over `B`, let `a : Amb ⟶ X` be étale and
let `b : X ⟶ Bb` be a structure morphism.  Write `i = i₀ ≫ a`.  The kernel ideal sheaves of `i`
and of `i₀` are compared by a morphism `κ : a^*𝓘_i ⟶ 𝓘_{i₀}`, pinned by its composite with the
inclusion into the structure sheaf, and the sheaves of differentials by the inverse-image
comparison of [Stacks Project, Tag 03LU] followed by the étale-source localisation of
[Stacks Project, Tag 04CU].

This file proves that **those two comparisons intertwine the first arrow of the conormal sequence
of [Stacks Project, Tag 05ZA] at `i` with the first arrow at `i₀`.**  That is the one clause the
reduction of [Stacks Project, Tag 04CE] of an immersion to a closed immersion was missing.

## Main results

* `AlgebraicGeometry.Space.kernelConormalFirstMap_comp`: **the comparison of the two first
  arrows**, for an arbitrary comparison map `c` of [Stacks Project, Tag 04CX] and an arbitrary
  `κ` with the pinning property.
* `AlgebraicGeometry.Space.kernelConormalFirstMap_compPullbackMap`: the same at the canonical
  comparison `AlgebraicGeometry.Space.kernelIdealCompPullbackMap` of the kernel ideal sheaves,
  with no hypothesis on it.
* `AlgebraicGeometry.Space.kernelConormalFirstMap_etaleAmbient` and
  `AlgebraicGeometry.Space.kernelConormalFirstMap_etaleAmbient_compPullbackMap`: the two
  preceding results at the étale-source localisation of [Stacks Project, Tag 04CU], which is a
  comparison map of [Stacks Project, Tag 04CX] for the square whose top edge is the étale
  morphism and whose bottom edge is an identity.

## Implementation notes

**Every step of the transposition is carried at plain variables.**  The implementation notes of
`AlgebraicGeometry.Space.submoduleTranspose_eq_kernelConormalFirstMap_of_val_app_apply` record
that writing the hom-set bijection of [Stacks Project, Tag 03D7] out at
`AlgebraicGeometry.Space.kernelConormalFirstMap` does not fit the default heartbeat budget, and
the same holds here: a `congrArg` identifying the transpose of the left-hand side with
the iterated transpose exhausts the budget when `AlgebraicGeometry.Space.kernelIdealSheaf` and
`AlgebraicGeometry.Space.kernelIdealUnitDifferential` are in sight, while the same statement at a
plain sheaf of ideals and a plain morphism costs nothing.  So the four transposition steps —
naturality on the right, naturality on the left, the comparison of inverse images, and the
pinning of a morphism out of an inverse image by the sections of its transpose — are each a
declaration at plain variables, and the geometric proof only instantiates them.

For the same reason the transposes appearing in the hypotheses of those lemmas are written
through `AlgebraicGeometry.Space.submoduleTranspose` and through the **unit** of the adjunction,
never through `CategoryTheory.Adjunction.homEquiv`: the unit is what
`AlgebraicGeometry.Space.pullbackUnitDerivation` is already built from.

**Two definitional identifications dominate the cost, and no declaration may carry both.**  The
first is `CategoryTheory.Sheaf.ringSheaf` against the module sheaf of
`CategoryTheory.SheafOfModules.unit`, which every composite of the inclusion of a sheaf of ideals
with a universal derivation meets; the second is the object of a composite of two direct images
against the iterated object, which the comparison of direct images meets.  Each is `rfl`, each is
affordable once in a statement at plain variables, and a declaration whose statement carries both
does not elaborate inside ten times the heartbeat budget.  So the steps that would
meet both are split, and the lemma that supplies one of them is passed as a **hypothesis**
rather than composed into place: that is why
`AlgebraicGeometry.Space.moduleSheafFunctor_map_kernelIdealUnitDifferential_comp` takes its tail
`T` as a parameter together with the equation defining it, and why it keeps the last two factors
`Q` and `R` separate instead of reassociating them.

**The derivation is read on underlying sheaves of sets.**  The first arrow is the transpose of a
derivation restricted to the ideal sheaf, and a derivation is not a morphism of modules, so the
restriction cannot be split off as a composite of module maps.  It is a morphism of sheaves of
sets, `AlgebraicGeometry.Space.universalDerivationHom`, and that is the level at which the
comparison with the étale restriction is available:
`AlgebraicGeometry.Space.universalDerivationHom_comp_homEquiv` at
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`.  So the value
computation factors the restricted derivation through
`AlgebraicGeometry.Space.moduleSheafFunctor_map_submoduleDerivationHom`, works on sheaves of
sets, and comes back with `CategoryTheory.Sheaf.hom_congr_app_apply`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Amb Z Bb Bb' : AlgebraicSpaces B S hS}

/-! ### The transposition steps, at plain variables -/

/-- Composing with a pair of morphisms whose composite is the identity changes nothing. -/
private theorem comp_comp_cancel_of_comp_eq_id {C : Type*} [Category C] {A Y Y' : C}
    (w : A ⟶ Y) (a : Y ⟶ Y') (b : Y' ⟶ Y) (h : a ≫ b = 𝟙 Y) : (w ≫ a) ≫ b = w := by
  rw [Category.assoc, h, Category.comp_id]

/-- **Postcomposing the transpose of a morphism out of a sheaf of ideals.**  The transpose along
`f^* ⊣ f_*` of `u`, followed by `R`, is the transpose of `u` followed by the direct image of `R`.

This is naturality of the hom-set bijection of [Stacks Project, Tag 03D7] on the right, read
through `AlgebraicGeometry.Space.submoduleTranspose`. -/
theorem submoduleTranspose_comp (f : Z ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (M N : Modules.{u, u} B S hS Z.1 Z.2)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj M) (R : M ⟶ N) :
    submoduleTranspose B S hS f I M u ≫ R =
      submoduleTranspose B S hS f I N (u ≫ (modulePushforward B S hS f).map R) :=
  ((modulePullbackAdjunction B S hS f).homEquiv_naturality_right_symm u R).symm

/-- **A morphism out of an inverse image of a sheaf of ideals is pinned by the sections of its
transpose.**  If the transpose of `k` along `g^* ⊣ g_*` — the unit of that adjunction followed by
the direct image of `k` — agrees with `q` on sections, then `k` is the transpose of `q`. -/
theorem eq_submoduleTranspose_of_val_app_apply (g : Amb ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (P : Modules.{u, u} B S hS Amb.1 Amb.2)
    (k : (modulePullback B S hS g).obj I.toSheafOfModules ⟶ P)
    (q : I.toSheafOfModules ⟶ (modulePushforward B S hS g).obj P)
    (hq : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (q.val.app U)) x =
        (ModuleCat.Hom.hom
          (((modulePullbackAdjunction B S hS g).unit.app I.toSheafOfModules ≫
            (modulePushforward B S hS g).map k).val.app U)) x) :
    k = submoduleTranspose B S hS g I P q := by
  refine Eq.trans ?_ (congrArg (submoduleTranspose B S hS g I P)
    (?_ : ((modulePullbackAdjunction B S hS g).homEquiv I.toSheafOfModules P) k = q))
  · exact (((modulePullbackAdjunction B S hS g).homEquiv I.toSheafOfModules P).symm_apply_apply
      k).symm
  · refine Eq.trans ((modulePullbackAdjunction B S hS g).homEquiv_unit _ _ k) ?_
    ext U x
    exact (hq U x).symm

/-- **The comparison of inverse images of [Stacks Project, Tag 03LU] absorbed into the
transpose.**  For `f : Z ⟶ Amb` and `g : Amb ⟶ X`, the comparison
`(f ≫ g)^*I ⟶ f^*(g^*I)`, followed by the inverse image along `f` of a morphism
`κ : g^*I ⟶ J` and by the transpose along `f^* ⊣ f_*` of `u`, is the transpose along
`(f ≫ g)^* ⊣ (f ≫ g)_*` of `w`, as soon as `κ ≫ u` is the transpose along `g^* ⊣ g_*` of `w`
read in `g_*(f_*N)`.

This is where the comparison of [Stacks Project, Tag 03LU] disappears: it is
`CategoryTheory.Adjunction.leftAdjointUniq` of two left adjoints of `(f ≫ g)_*`
(`AlgebraicGeometry.Space.modulePullbackCompIso_eq`), so precomposing with it inside a transpose
only swaps which adjunction the transpose is taken over —
`AlgebraicGeometry.Space.homEquiv_modulePullbackCompIso_inv_app_comp`. -/
theorem modulePullbackCompIso_inv_app_comp_submoduleTranspose (f : Z ⟶ Amb) (g : Amb ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (J : (SheafOfModules.unit (structureRingSheaf B S hS Amb)).Submodule)
    (N : Modules.{u, u} B S hS Z.1 Z.2)
    (κ : (modulePullback B S hS g).obj I.toSheafOfModules ⟶ J.toSheafOfModules)
    (u : J.toSheafOfModules ⟶ (modulePushforward B S hS f).obj N)
    (w : I.toSheafOfModules ⟶ (modulePushforward B S hS (f ≫ g)).obj N)
    (hw : κ ≫ u = submoduleTranspose B S hS g I ((modulePushforward B S hS f).obj N)
      (w ≫ (modulePushforwardCompIso B S hS f g).inv.app N)) :
    (modulePullbackCompIso B S hS f g).inv.app I.toSheafOfModules ≫
        (modulePullback B S hS f).map κ ≫ submoduleTranspose B S hS f J N u =
      submoduleTranspose B S hS (f ≫ g) I N w := by
  refine ((modulePullbackAdjunction B S hS (f ≫ g)).homEquiv I.toSheafOfModules N).injective ?_
  refine Eq.trans (homEquiv_modulePullbackCompIso_inv_app_comp B S hS f g I.toSheafOfModules N
    ((modulePullback B S hS f).map κ ≫ submoduleTranspose B S hS f J N u)) ?_
  refine Eq.trans ?_ (homEquiv_submoduleTranspose B S hS (f ≫ g) I N w).symm
  refine Eq.trans (congrArg (fun m ↦ ((modulePullbackAdjunction B S hS g).homEquiv
        I.toSheafOfModules ((modulePushforward B S hS f).obj N)) m ≫
      (modulePushforwardCompIso B S hS f g).hom.app N)
    ((((modulePullbackAdjunction B S hS f).homEquiv_naturality_left κ
          (submoduleTranspose B S hS f J N u)).trans
        (congrArg (fun m ↦ κ ≫ m) (homEquiv_submoduleTranspose B S hS f J N u))).trans hw)) ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ (modulePushforwardCompIso B S hS f g).hom.app N)
    (homEquiv_submoduleTranspose B S hS g I ((modulePushforward B S hS f).obj N)
      (w ≫ (modulePushforwardCompIso B S hS f g).inv.app N))) ?_
  exact comp_comp_cancel_of_comp_eq_id w _ _
    ((modulePushforwardCompIso B S hS f g).inv_hom_id_app N)

/-- **The transpose of the composite of two inverse-image comparisons at a sheaf of
differentials.**  For `f : Z ⟶ Amb`, `g : Amb ⟶ X` and `c : g^*M ⟶ M'`, the transpose along
`(f ≫ g)^* ⊣ (f ≫ g)_*` of the comparison of [Stacks Project, Tag 03LU] followed by the inverse
image along `f` of `c`, read in `g_*(f_*(f^*M'))`, is the transpose of `c` followed by the direct
image along `g` of the unit of `f^* ⊣ f_*`.

Both the unit and the comparison of direct images are moved by naturality alone; this is the
step that turns a statement about the composite `f ≫ g` into one about `g`, where the
étale-source localisation of [Stacks Project, Tag 04CU] is characterised. -/
theorem unit_comp_modulePushforward_map_modulePullbackCompIso_inv_app_comp
    (f : Z ⟶ Amb) (g : Amb ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (M' : Modules.{u, u} B S hS Amb.1 Amb.2)
    (c : (modulePullback B S hS g).obj M ⟶ M') :
    (modulePullbackAdjunction B S hS (f ≫ g)).unit.app M ≫
        ((modulePushforward B S hS (f ≫ g)).map
            ((modulePullbackCompIso B S hS f g).inv.app M ≫
              (modulePullback B S hS f).map c) ≫
          (modulePushforwardCompIso B S hS f g).inv.app
            ((modulePullback B S hS f).obj M')) =
      ((modulePullbackAdjunction B S hS g).homEquiv M M' c) ≫
        (modulePushforward B S hS g).map
          ((modulePullbackAdjunction B S hS f).unit.app M') := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  have hu : ((modulePullbackAdjunction B S hS (f ≫ g)).homEquiv M
        ((modulePullback B S hS f).obj M'))
      ((modulePullbackCompIso B S hS f g).inv.app M ≫ (modulePullback B S hS f).map c) =
      ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M ≫
        (modulePushforward B S hS (f ≫ g)).map
          ((modulePullbackCompIso B S hS f g).inv.app M ≫
            (modulePullback B S hS f).map c)) :=
    (modulePullbackAdjunction B S hS (f ≫ g)).homEquiv_unit _ _ _
  have hf : ((modulePullbackAdjunction B S hS f).homEquiv ((modulePullback B S hS g).obj M)
        ((modulePullback B S hS f).obj M')) ((modulePullback B S hS f).map c) =
      c ≫ (modulePullbackAdjunction B S hS f).unit.app M' := by
    refine Eq.trans ((modulePullbackAdjunction B S hS f).homEquiv_unit _ _ _) ?_
    exact (modulePullbackAdjunction B S hS f).unit_naturality c
  have h1 : ((modulePullbackAdjunction B S hS (f ≫ g)).homEquiv M
        ((modulePullback B S hS f).obj M'))
      ((modulePullbackCompIso B S hS f g).inv.app M ≫ (modulePullback B S hS f).map c) =
      (((modulePullbackAdjunction B S hS g).homEquiv M M') c ≫
          (modulePushforward B S hS g).map
            ((modulePullbackAdjunction B S hS f).unit.app M')) ≫
        (modulePushforwardCompIso B S hS f g).hom.app
          ((modulePullback B S hS f).obj M') := by
    refine Eq.trans (homEquiv_modulePullbackCompIso_inv_app_comp B S hS f g M
      ((modulePullback B S hS f).obj M') ((modulePullback B S hS f).map c)) ?_
    refine congrArg (fun m ↦ m ≫ (modulePushforwardCompIso B S hS f g).hom.app
      ((modulePullback B S hS f).obj M')) ?_
    refine Eq.trans (congrArg ((modulePullbackAdjunction B S hS g).homEquiv M
      ((modulePushforward B S hS f).obj ((modulePullback B S hS f).obj M'))) hf) ?_
    exact (modulePullbackAdjunction B S hS g).homEquiv_naturality_right c
      ((modulePullbackAdjunction B S hS f).unit.app M')
  refine Eq.trans (congrArg (fun m ↦ m ≫ (modulePushforwardCompIso B S hS f g).inv.app
      ((modulePullback B S hS f).obj M')) (hu.symm.trans h1)) ?_
  exact comp_comp_cancel_of_comp_eq_id _ _ _
    ((modulePushforwardCompIso B S hS f g).hom_inv_id_app ((modulePullback B S hS f).obj M'))

/-- **The restriction of a derivation to a sheaf of ideals, on underlying sheaves of sets.**  It
is the inclusion of the sheaf of ideals into the structure sheaf followed by any morphism of
sheaves of sets whose value on a local section is the value of the derivation on it.

A derivation is not a morphism of modules, so the restriction cannot be split off inside the
category of `𝒪_X`-modules; on underlying sheaves of sets it can, and that is the level at which
the comparison of [Stacks Project, Tag 04CU] with the universal derivations is stated. -/
theorem moduleSheafFunctor_map_submoduleDerivationHom
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (N : Modules.{u, u} B S hS X.1 X.2) (D : N.val.Derivation' φ.hom)
    (hann : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (r : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      r ∈ I.obj U →
        letI : Module ((structureRingSheaf B S hS X).obj.obj U) (N.val.obj U) :=
          (N.val.obj U).isModule
        ∀ m : N.val.obj U, r • m = 0)
    (δ : CategoryTheory.Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)
    (hδ : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (t : (structureRingSheaf B S hS X).obj.obj U), δ.hom.app U t = D.d t) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (submoduleDerivationHom B S hS I N D hann) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map I.ι ≫ δ :=
  Sheaf.hom_ext_sections fun U x ↦ (hδ U x.1).symm

/-- **The transpose of the inverse image of the inclusion of a sheaf of ideals, followed by a
morphism.**  The unit of `g^* ⊣ g_*` at the sheaf of ideals, followed by the direct image of
`g^*ι ≫ θ`, is the inclusion followed by the transpose of `θ`.

This is naturality of the hom-set bijection of [Stacks Project, Tag 03D7] on the left, which is
what moves the inclusion of the sheaf of ideals out of the inverse image. -/
theorem unit_comp_modulePushforward_map_ι_comp (g : Amb ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (P : Modules.{u, u} B S hS Amb.1 Amb.2)
    (θ : (modulePullback B S hS g).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)) ⟶ P) :
    (modulePullbackAdjunction B S hS g).unit.app I.toSheafOfModules ≫
        (modulePushforward B S hS g).map
          ((modulePullback B S hS g).map I.ι ≫ θ) =
      I.ι ≫ ((modulePullbackAdjunction B S hS g).homEquiv
        (SheafOfModules.unit (structureRingSheaf B S hS X)) P) θ :=
  (((modulePullbackAdjunction B S hS g).homEquiv_unit I.toSheafOfModules P _).symm).trans
    ((modulePullbackAdjunction B S hS g).homEquiv_naturality_left I.ι θ)

/-! ### The adjoint first arrow on underlying sheaves of sets -/

/-- **The adjoint form of the first arrow of [Stacks Project, Tag 05ZA], on underlying sheaves of
sets.**  It is the inclusion of the kernel ideal sheaf into the structure sheaf, followed by the
universal derivation `d_{Y/B}` and the unit of `f^* ⊣ f_*`.

The derivation is not a morphism of modules, so this factorisation is available only after the
module structures are forgotten; it is what lets the comparison of [Stacks Project, Tag 04CU]
with the universal derivations be applied to the first arrow. -/
theorem moduleSheafFunctor_map_kernelIdealUnitDifferential (f : Z ⟶ X) (p : X ⟶ Bb) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (kernelIdealUnitDifferential B S hS f p) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (kernelIdealSheaf B S hS f).ι ≫
        universalDerivationHom B S hS p ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((modulePullbackAdjunction B S hS f).unit.app
              (sheafOfDifferentials B S hS p)) :=
  moduleSheafFunctor_map_submoduleDerivationHom B S hS (kernelIdealSheaf B S hS f) _
    (pullbackUnitDerivation B S hS f p)
    (fun U r hr m ↦ kernelIdealAt_smul_modulePushforward_eq_zero B S hS f _ U r hr m) _
    (fun _ _ ↦ rfl)

/-! ### The two sides of the comparison, read on underlying sheaves of sets -/

/-- **The restriction of a derivation to a sheaf of ideals, followed by a morphism, on
underlying sheaves of sets.**
`AlgebraicGeometry.Space.moduleSheafFunctor_map_submoduleDerivationHom` composed with a further
morphism. -/
theorem moduleSheafFunctor_map_submoduleDerivationHom_comp
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (N N' : Modules.{u, u} B S hS X.1 X.2) (D : N.val.Derivation' φ.hom)
    (hann : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (r : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      r ∈ I.obj U →
        letI : Module ((structureRingSheaf B S hS X).obj.obj U) (N.val.obj U) :=
          (N.val.obj U).isModule
        ∀ m : N.val.obj U, r • m = 0)
    (δ : CategoryTheory.Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)
    (hδ : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (t : (structureRingSheaf B S hS X).obj.obj U), δ.hom.app U t = D.d t)
    (Q : N ⟶ N') :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (submoduleDerivationHom B S hS I N D hann ≫ Q) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map I.ι ≫
        δ ≫ (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map Q :=
  (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).trans
      (eq_whisker (moduleSheafFunctor_map_submoduleDerivationHom B S hS I N D hann δ hδ)
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map Q))).trans
    (Category.assoc _ _ _)

/-- **The transpose of a comparison map of [Stacks Project, Tag 04CX] for the composite `f ≫ g`,
read through the comparison of inverse images of [Stacks Project, Tag 03LU].**  The universal
derivation `d_{X/B}` followed by the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*`, then by the direct image of
the composite of the inverse-image comparison with `f^*c`, and finally by the comparison of direct
images, is the composite `g_*d_{Amb/B'} ∘ g^♯` of [Stacks Project, Tag 04CX] followed by the direct
image along `g` of the unit of `f^* ⊣ f_*`.

The hypothesis on `c` is exactly the characterising property of [Stacks Project, Tag 04CX] for the
square with top edge `g`, so for an étale `g` it is satisfied by the étale-source localisation of
[Stacks Project, Tag 04CU],
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`. -/
theorem universalDerivationHom_comp_modulePullbackCompIso_inv_app_comp
    (f : Z ⟶ Amb) (g : Amb ⟶ X) (p : X ⟶ Bb) (p' : Amb ⟶ Bb')
    {c : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g p p' c) :
    (universalDerivationHom B S hS p ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app
              (sheafOfDifferentials B S hS p))) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePushforward B S hS (f ≫ g)).map
              ((modulePullbackCompIso B S hS f g).inv.app
                  (sheafOfDifferentials B S hS p) ≫
                (modulePullback B S hS f).map c) ≫
            (modulePushforwardCompIso B S hS f g).inv.app
              ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS p'))) =
      pushforwardUniversalDerivationHom B S hS g p' ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePushforward B S hS g).map
            ((modulePullbackAdjunction B S hS f).unit.app
              (sheafOfDifferentials B S hS p'))) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (congrArg
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
    (unit_comp_modulePushforward_map_modulePullbackCompIso_inv_app_comp B S hS f g
      (sheafOfDifferentials B S hS p) (sheafOfDifferentials B S hS p') c))) ?_
  refine Eq.trans (whisker_eq _
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact eq_whisker (universalDerivationHom_comp_homEquiv B S hS g p p' hc) _

/-- **The restriction of sections to an open-or-étale ambient space, followed by the restriction
of a derivation, on underlying sheaves of sets.**  Let `κ : g^*I ⟶ J` be pinned by `θ` through the
inclusions into the two structure sheaves, and let `v` be a morphism out of `J` whose underlying
morphism of sheaves of sets factors as the inclusion of `J` followed by `ε`.  Then the transpose
of `κ ≫ v` is the inclusion of `I`, the transpose of `θ`, and the direct image of `ε`.

Stated at plain variables; the geometric instance takes `θ` to be the comparison
`g^*𝒪_X ⟶ 𝒪_Amb`, whose transpose is the structure map `g^♯` by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_homEquiv_structureModulePullbackMap`, and `ε` to
be the universal derivation followed by the unit. -/
theorem moduleSheafFunctor_map_unit_comp_modulePushforward_map_comp (g : Amb ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (J : (SheafOfModules.unit (structureRingSheaf B S hS Amb)).Submodule)
    (P : Modules.{u, u} B S hS Amb.1 Amb.2)
    (κ : (modulePullback B S hS g).obj I.toSheafOfModules ⟶ J.toSheafOfModules)
    (θ : (modulePullback B S hS g).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS Amb))
    (hκ : κ ≫ J.ι = (modulePullback B S hS g).map I.ι ≫ θ)
    (v : J.toSheafOfModules ⟶ P)
    (ε : CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Amb)
        (SheafOfModules.unit (structureRingSheaf B S hS Amb)) ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Amb) P)
    (hv : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Amb)).map v =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Amb)).map J.ι ≫ ε) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS g).unit.app I.toSheafOfModules ≫
          (modulePushforward B S hS g).map (κ ≫ v)) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map I.ι ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            (((modulePullbackAdjunction B S hS g).homEquiv
              (SheafOfModules.unit (structureRingSheaf B S hS X))
              (SheafOfModules.unit (structureRingSheaf B S hS Amb))) θ) ≫
          (smallEtaleDirectImage B S hS g).map ε := by
  have h1 : (modulePullbackAdjunction B S hS g).unit.app I.toSheafOfModules ≫
        (modulePushforward B S hS g).map (κ ≫ v) =
      ((modulePullbackAdjunction B S hS g).unit.app I.toSheafOfModules ≫
          (modulePushforward B S hS g).map κ) ≫ (modulePushforward B S hS g).map v :=
    (whisker_eq _ ((modulePushforward B S hS g).map_comp κ v)).trans
      (Category.assoc _ _ _).symm
  have h3 : ((modulePullbackAdjunction B S hS g).unit.app I.toSheafOfModules ≫
          (modulePushforward B S hS g).map κ) ≫ (modulePushforward B S hS g).map J.ι =
      I.ι ≫ (((modulePullbackAdjunction B S hS g).homEquiv
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS Amb))) θ) :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ ((modulePushforward B S hS g).map_comp κ J.ι).symm).trans
        ((whisker_eq _ (congrArg (modulePushforward B S hS g).map hκ)).trans
          (unit_comp_modulePushforward_map_ι_comp B S hS g I
            (SheafOfModules.unit (structureRingSheaf B S hS Amb)) θ)))
  refine Eq.trans (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map h1) ?_
  refine Eq.trans ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _) ?_
  refine Eq.trans (whisker_eq _
    ((moduleSheafFunctor_map_modulePushforward_map B S hS g v).trans
      ((congrArg (smallEtaleDirectImage B S hS g).map hv).trans
        ((smallEtaleDirectImage B S hS g).map_comp _ _)))) ?_
  have h4 : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePullbackAdjunction B S hS g).unit.app I.toSheafOfModules ≫
            (modulePushforward B S hS g).map κ) ≫
        (smallEtaleDirectImage B S hS g).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Amb)).map J.ι) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map I.ι ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (((modulePullbackAdjunction B S hS g).homEquiv
            (SheafOfModules.unit (structureRingSheaf B S hS X))
            (SheafOfModules.unit (structureRingSheaf B S hS Amb))) θ) := by
    refine Eq.trans (whisker_eq _
      (moduleSheafFunctor_map_modulePushforward_map B S hS g J.ι).symm) ?_
    refine Eq.trans ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).symm ?_
    refine Eq.trans (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map h3) ?_
    exact (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact (eq_whisker h4 ((smallEtaleDirectImage B S hS g).map ε)).trans (Category.assoc _ _ _)

/-- **The structure map and the universal derivation reassembled into the composite of
[Stacks Project, Tag 04CX].**  The transpose of the comparison `g^*𝒪_X ⟶ 𝒪_Amb`, followed by the
direct image along `g` of the universal derivation `d_{Amb/Bb'}` and of a further morphism `ψ`,
is the composite `g_*d_{Amb/Bb'} ∘ g^♯` followed by the direct image of `ψ`.

This is the shape in which the two sides of the comparison meet: the one coming from the
inverse image of the ideal sheaf arrives as `g^♯` followed by a direct image, the one coming
from the universal derivation of `X` arrives as
`AlgebraicGeometry.Space.pushforwardUniversalDerivationHom`, and this identifies them. -/
theorem homEquiv_structureModulePullbackMap_comp_universalDerivationHom_comp (g : Amb ⟶ X)
    (p' : Amb ⟶ Bb') (P : Modules.{u, u} B S hS Amb.1 Amb.2)
    (ψ : sheafOfDifferentials B S hS p' ⟶ P) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (((modulePullbackAdjunction B S hS g).homEquiv
            (SheafOfModules.unit (structureRingSheaf B S hS X))
            (SheafOfModules.unit (structureRingSheaf B S hS Amb)))
              (structureModulePullbackMap B S hS g)) ≫
        (smallEtaleDirectImage B S hS g).map
          (universalDerivationHom B S hS p' ≫
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Amb)).map ψ) =
      pushforwardUniversalDerivationHom B S hS g p' ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePushforward B S hS g).map ψ) := by
  refine Eq.trans (whisker_eq _ ((smallEtaleDirectImage B S hS g).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine eq_whisker ?_ ((smallEtaleDirectImage B S hS g).map
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Amb)).map ψ))
  exact (eq_whisker (moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS g)
    ((smallEtaleDirectImage B S hS g).map (universalDerivationHom B S hS p'))).trans
      (pushforwardUniversalDerivationHom_eq B S hS g p').symm

/-- **The adjoint first arrow of [Stacks Project, Tag 05ZA] followed by a morphism, pinned on
sections.**  The adjoint first arrow at `f`, followed by `Q` and then `R`, is on underlying
sheaves of sets the inclusion of the kernel ideal sheaf followed by any `T` that `d_{X/Bb}`, the
unit of `f^* ⊣ f_*` and `Q ≫ R` compose to.

The last two factors are kept apart because the comparison below produces them separately — the
direct image of the inverse-image comparison, and then the comparison of direct images — and
reassociating them at the geometric terms is itself past the budget.

Stated at plain variables, and it is here that the module sheaf of the unit module is identified
with the sheaf of rings: `T` starts at `CategoryTheory.Sheaf.ringSheaf`, while the inclusion of
the kernel ideal sheaf lands in the module sheaf of `CategoryTheory.SheafOfModules.unit`.  The two
are definitionally equal, and the identification is affordable in a statement at plain variables
but **not** in a unification against the geometric terms of the comparison below, where it does
not terminate inside ten times the heartbeat budget.  Taking the hypothesis on
sections, rather than as an equation of morphisms of sheaves of sets, is what confines it here. -/
theorem moduleSheafFunctor_map_kernelIdealUnitDifferential_comp (f : Z ⟶ X) (p : X ⟶ Bb)
    (M P : Modules.{u, u} B S hS X.1 X.2)
    (Q : (modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS p)) ⟶ M) (R : M ⟶ P)
    (T : CategoryTheory.Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) P)
    (hT : (universalDerivationHom B S hS p ≫
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
              ((modulePullbackAdjunction B S hS f).unit.app
                (sheafOfDifferentials B S hS p))) ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (Q ≫ R) = T) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((kernelIdealUnitDifferential B S hS f p ≫ Q) ≫ R) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (kernelIdealSheaf B S hS f).ι ≫ T := by
  refine Sheaf.hom_ext_sections fun U x ↦ ?_
  refine Eq.trans ?_ (congrArg (fun m ↦
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
      (kernelIdealSheaf B S hS f).ι ≫ m).hom.app U x) hT)
  rfl

/-- **An equation of morphisms of modules read on sections, from the equation of the underlying
morphisms of sheaves of sets.**  Stated at plain variables: at the geometric instance the
reconciliation of the two spellings of a section is what costs, and the heartbeat budget is per
declaration. -/
theorem val_app_apply_of_moduleSheafFunctor_map_eq
    {M N : Modules.{u, u} B S hS X.1 X.2} {a b : M ⟶ N}
    (h : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map a =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map b)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : M.val.obj U) :
    (ModuleCat.Hom.hom (a.val.app U)) x = (ModuleCat.Hom.hom (b.val.app U)) x :=
  Sheaf.hom_congr_app_apply h U x

/-- **A morphism out of an inverse image of a sheaf of ideals is pinned by the underlying
morphism of sheaves of sets of its transpose.**
`AlgebraicGeometry.Space.eq_submoduleTranspose_of_val_app_apply` with its hypothesis read as one
equation of morphisms of sheaves of sets rather than as a family of equations on sections.

Stated at plain variables, and this is the form the geometric comparison consumes: the two
reconciliations it needs — sections of a sheaf of modules against sections of the underlying
sheaf of sets, and the unit of the adjunction against the hom-set bijection — are both carried
out here, where no geometric term is in sight. -/
theorem eq_submoduleTranspose_of_moduleSheafFunctor_map_eq (g : Amb ⟶ X)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (P : Modules.{u, u} B S hS Amb.1 Amb.2)
    (k : (modulePullback B S hS g).obj I.toSheafOfModules ⟶ P)
    (q : I.toSheafOfModules ⟶ (modulePushforward B S hS g).obj P)
    (hq : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map q =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS g).unit.app I.toSheafOfModules ≫
          (modulePushforward B S hS g).map k)) :
    k = submoduleTranspose B S hS g I P q :=
  eq_submoduleTranspose_of_val_app_apply B S hS g I P k q
    (fun U x ↦ val_app_apply_of_moduleSheafFunctor_map_eq B S hS hq U x)

/-! ### The final assembly, at plain variables -/

/-- **The two adjoint first arrows agree on sections of the kernel ideal sheaf.**  Let
`f : Z ⟶ Amb` and `g : Amb ⟶ X`, let `c : g^*Ω_{X/Bb} ⟶ Ω_{Amb/Bb'}` be a comparison map of
[Stacks Project, Tag 04CX], and let `κ : g^*𝓘_{f ≫ g} ⟶ 𝓘_f` be pinned through the inclusions of
the two kernel ideal sheaves into their structure sheaves.  Then the transpose along `g^* ⊣ g_*`
of `κ` followed by the adjoint first arrow at `f` is, on underlying sheaves of sets, the adjoint
first arrow at `f ≫ g` followed by the comparison of inverse images of
[Stacks Project, Tag 03LU], by `f^*c`, and by the comparison of direct images.

This is the whole content of the comparison.  Both sides are the inclusion of `𝓘_{f ≫ g}`
followed by the composite `g_*d_{Amb/Bb'} ∘ g^♯` of [Stacks Project, Tag 04CX] and the direct
image of the unit of `f^* ⊣ f_*`: on the left because `κ` is pinned by `g^♯`, on the right
because `c` has the characterising property of [Stacks Project, Tag 04CX]. -/
theorem moduleSheafFunctor_map_unit_comp_kernelIdealUnitDifferential_comp
    (f : Z ⟶ Amb) (g : Amb ⟶ X) (p : X ⟶ Bb) (p' : Amb ⟶ Bb')
    {c : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g p p' c)
    (κ : (modulePullback B S hS g).obj
        (kernelIdealSheaf B S hS (f ≫ g)).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS f).toSheafOfModules)
    (hκ : κ ≫ (kernelIdealSheaf B S hS f).ι =
      (modulePullback B S hS g).map (kernelIdealSheaf B S hS (f ≫ g)).ι ≫
        structureModulePullbackMap B S hS g) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS g).unit.app
            (kernelIdealSheaf B S hS (f ≫ g)).toSheafOfModules ≫
          (modulePushforward B S hS g).map
            (κ ≫ kernelIdealUnitDifferential B S hS f p')) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((kernelIdealUnitDifferential B S hS (f ≫ g) p ≫
            (modulePushforward B S hS (f ≫ g)).map
              ((modulePullbackCompIso B S hS f g).inv.app
                  (sheafOfDifferentials B S hS p) ≫
                (modulePullback B S hS f).map c)) ≫
          (modulePushforwardCompIso B S hS f g).inv.app
            ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS p'))) := by
  have htail := homEquiv_structureModulePullbackMap_comp_universalDerivationHom_comp B S hS g p'
    ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS p')))
    ((modulePullbackAdjunction B S hS f).unit.app (sheafOfDifferentials B S hS p'))
  have hleft := (moduleSheafFunctor_map_unit_comp_modulePushforward_map_comp B S hS g
      (kernelIdealSheaf B S hS (f ≫ g)) (kernelIdealSheaf B S hS f) _ κ
      (structureModulePullbackMap B S hS g) hκ
      (kernelIdealUnitDifferential B S hS f p') _
      (moduleSheafFunctor_map_kernelIdealUnitDifferential B S hS f p')).trans
    (whisker_eq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
      (kernelIdealSheaf B S hS (f ≫ g)).ι) htail)
  have hright := moduleSheafFunctor_map_kernelIdealUnitDifferential_comp B S hS (f ≫ g) p _ _ _ _ _
    (universalDerivationHom_comp_modulePullbackCompIso_inv_app_comp B S hS f g p p' hc)
  exact hleft.trans hright.symm

/-- **The first arrow of the conormal sequence of [Stacks Project, Tag 05ZA] across a comparison
map of [Stacks Project, Tag 04CX].**  Let `f : Z ⟶ Amb` and `g : Amb ⟶ X`, let
`c : g^*Ω_{X/Bb} ⟶ Ω_{Amb/Bb'}` be a comparison map of [Stacks Project, Tag 04CX], and let
`κ : g^*𝓘_{f ≫ g} ⟶ 𝓘_f` be any comparison of the kernel ideal sheaves pinned through the
inclusions into the two structure sheaves — as the map of [Stacks Project, Tag 03LW] attached to
the square is, by `AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι`.  Then the comparison of
inverse images of [Stacks Project, Tag 03LU] together with `κ` on the left, and together with `c`
on the right, intertwine the first arrow of `f ≫ g` with the first arrow of `f`.

Both sides are transposes of morphisms out of `𝓘_{f ≫ g}`, so the comparison is an equality of
two sections formulas, and that is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_unit_comp_kernelIdealUnitDifferential_comp`; the
transposition itself is carried by
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_comp_submoduleTranspose` on the left and
`AlgebraicGeometry.Space.submoduleTranspose_comp` on the right. -/
theorem kernelConormalFirstMap_comp (f : Z ⟶ Amb) (g : Amb ⟶ X) (p : X ⟶ Bb) (p' : Amb ⟶ Bb')
    {c : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g p p' c)
    (κ : (modulePullback B S hS g).obj
        (kernelIdealSheaf B S hS (f ≫ g)).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS f).toSheafOfModules)
    (hκ : κ ≫ (kernelIdealSheaf B S hS f).ι =
      (modulePullback B S hS g).map (kernelIdealSheaf B S hS (f ≫ g)).ι ≫
        structureModulePullbackMap B S hS g) :
    (modulePullbackCompIso B S hS f g).inv.app
          (kernelIdealSheaf B S hS (f ≫ g)).toSheafOfModules ≫
        (modulePullback B S hS f).map κ ≫ kernelConormalFirstMap B S hS f p' =
      kernelConormalFirstMap B S hS (f ≫ g) p ≫
        (modulePullbackCompIso B S hS f g).inv.app (sheafOfDifferentials B S hS p) ≫
          (modulePullback B S hS f).map c := by
  have hw := eq_submoduleTranspose_of_moduleSheafFunctor_map_eq B S hS g
    (kernelIdealSheaf B S hS (f ≫ g))
    ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS p')))
    (κ ≫ kernelIdealUnitDifferential B S hS f p') _
    (moduleSheafFunctor_map_unit_comp_kernelIdealUnitDifferential_comp B S hS f g p p' hc
      κ hκ).symm
  have hAmb := submoduleTranspose_eq_kernelConormalFirstMap_of_val_app_apply B S hS f p'
    (kernelIdealUnitDifferential B S hS f p')
    (kernelIdealUnitDifferential_val_app_apply B S hS f p')
  have hTot := submoduleTranspose_eq_kernelConormalFirstMap_of_val_app_apply B S hS (f ≫ g) p
    (kernelIdealUnitDifferential B S hS (f ≫ g) p)
    (kernelIdealUnitDifferential_val_app_apply B S hS (f ≫ g) p)
  refine Eq.trans (congrArg (fun m ↦ (modulePullbackCompIso B S hS f g).inv.app
      (kernelIdealSheaf B S hS (f ≫ g)).toSheafOfModules ≫
    (modulePullback B S hS f).map κ ≫ m) hAmb.symm) ?_
  refine Eq.trans (modulePullbackCompIso_inv_app_comp_submoduleTranspose B S hS f g
    (kernelIdealSheaf B S hS (f ≫ g)) (kernelIdealSheaf B S hS f)
    ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS p')) κ
    (kernelIdealUnitDifferential B S hS f p') _ hw) ?_
  refine Eq.trans (submoduleTranspose_comp B S hS (f ≫ g)
    (kernelIdealSheaf B S hS (f ≫ g))
    ((modulePullback B S hS (f ≫ g)).obj (sheafOfDifferentials B S hS p))
    ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS p'))
    (kernelIdealUnitDifferential B S hS (f ≫ g) p)
    ((modulePullbackCompIso B S hS f g).inv.app (sheafOfDifferentials B S hS p) ≫
      (modulePullback B S hS f).map c)).symm ?_
  exact eq_whisker hTot
    ((modulePullbackCompIso B S hS f g).inv.app (sheafOfDifferentials B S hS p) ≫
      (modulePullback B S hS f).map c)

/-! ### The comparison of the kernel ideal sheaves in degree one -/

/-- **The pinning of a comparison of sheaves of ideals, transported along equalities of the two
ideals.**  Proved by `subst` at plain variables, before any geometric term is in sight.

The equalities of the underlying sheaves of modules are separate hypotheses rather than
`congrArg` of the equalities of the submodules: in the application the equality at hand has a
different proof term, and by proof irrelevance `CategoryTheory.eqToHom` does not depend on
which. -/
theorem eqToHom_comp_comp_eqToHom_comp_ι (g : Amb ⟶ X)
    {I I' : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule}
    {J J' : (SheafOfModules.unit (structureRingSheaf B S hS Amb)).Submodule}
    (hI : I = I') (hJ : J = J')
    (hIo : I'.toSheafOfModules = I.toSheafOfModules)
    (hJo : J.toSheafOfModules = J'.toSheafOfModules)
    (κ : (modulePullback B S hS g).obj I.toSheafOfModules ⟶ J.toSheafOfModules)
    (hκ : κ ≫ J.ι =
      (modulePullback B S hS g).map I.ι ≫ structureModulePullbackMap B S hS g) :
    ((modulePullback B S hS g).map (eqToHom hIo) ≫ κ ≫ eqToHom hJo) ≫ J'.ι =
      (modulePullback B S hS g).map I'.ι ≫ structureModulePullbackMap B S hS g := by
  subst hI
  subst hJ
  refine Eq.trans (eq_whisker ?_ J.ι) hκ
  exact ((eq_whisker ((modulePullback B S hS g).map_id I.toSheafOfModules)
        (κ ≫ eqToHom hJo)).trans
      (Category.id_comp (κ ≫ eqToHom hJo))).trans (Category.comp_id κ)

/-- **The comparison `g^*𝓘_{f ≫ g} ⟶ 𝓘_f` of the kernel ideal sheaves of a morphism and of its
composite with `g`**: the map of [Stacks Project, Tag 09RS] in degree one, read at the kernel
ideal sheaves themselves rather than at their first powers. -/
noncomputable def kernelIdealCompPullbackMap (f : Z ⟶ Amb) (g : Amb ⟶ X) :
    (modulePullback B S hS g).obj
        (kernelIdealSheaf B S hS (f ≫ g)).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS f).toSheafOfModules :=
  (modulePullback B S hS g).map (eqToHom (congrArg
      (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule ↦
        K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS (f ≫ g)).symm)) ≫
    kernelIdealSheafZPowPullbackMap B S hS f g 1 ≫
      eqToHom (congrArg
        (fun K : (SheafOfModules.unit (structureRingSheaf B S hS Amb)).Submodule ↦
          K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS f))

/-- **`AlgebraicGeometry.Space.kernelIdealCompPullbackMap` is pinned by pullback of regular
functions along `g`.**  Followed by the inclusion `𝓘_f ⊆ 𝒪_Amb` it is the inverse image along `g`
of the inclusion `𝓘_{f ≫ g} ⊆ 𝒪_X`, read in `𝒪_Amb` through
`AlgebraicGeometry.Space.structureModulePullbackMap`.

This discharges the hypothesis of
`AlgebraicGeometry.Space.kernelConormalFirstMap_comp` at the canonical comparison; it is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_comp_ι` in degree one. -/
theorem kernelIdealCompPullbackMap_comp_ι (f : Z ⟶ Amb) (g : Amb ⟶ X) :
    kernelIdealCompPullbackMap B S hS f g ≫ (kernelIdealSheaf B S hS f).ι =
      (modulePullback B S hS g).map (kernelIdealSheaf B S hS (f ≫ g)).ι ≫
        structureModulePullbackMap B S hS g :=
  eqToHom_comp_comp_eqToHom_comp_ι B S hS g
    (kernelIdealSheafZPow_one B S hS (f ≫ g)) (kernelIdealSheafZPow_one B S hS f) _ _
    (kernelIdealSheafZPowPullbackMap B S hS f g 1)
    (kernelIdealSheafZPowPullbackMap_comp_ι B S hS f g 1)

/-- **The comparison of the two first arrows at the canonical comparison of the kernel ideal
sheaves, with no hypothesis on it.**
`AlgebraicGeometry.Space.kernelConormalFirstMap_comp` with its pinning hypothesis discharged by
`AlgebraicGeometry.Space.kernelIdealCompPullbackMap_comp_ι`. -/
theorem kernelConormalFirstMap_compPullbackMap (f : Z ⟶ Amb) (g : Amb ⟶ X) (p : X ⟶ Bb)
    (p' : Amb ⟶ Bb')
    {c : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g p p' c) :
    (modulePullbackCompIso B S hS f g).inv.app
          (kernelIdealSheaf B S hS (f ≫ g)).toSheafOfModules ≫
        (modulePullback B S hS f).map (kernelIdealCompPullbackMap B S hS f g) ≫
          kernelConormalFirstMap B S hS f p' =
      kernelConormalFirstMap B S hS (f ≫ g) p ≫
        (modulePullbackCompIso B S hS f g).inv.app (sheafOfDifferentials B S hS p) ≫
          (modulePullback B S hS f).map c :=
  kernelConormalFirstMap_comp B S hS f g p p' hc (kernelIdealCompPullbackMap B S hS f g)
    (kernelIdealCompPullbackMap_comp_ι B S hS f g)

/-! ### The comparison across an étale change of ambient space -/

/-- **The first arrow of the conormal sequence of [Stacks Project, Tag 05ZA] across an étale
change of ambient space.**  Let `i₀ : Z ⟶ Amb`, let `ι : Amb ⟶ X` be étale, let `b : X ⟶ Bb`, and
let `κ : ι^*𝓘_{i₀ ≫ ι} ⟶ 𝓘_{i₀}` be any comparison of the kernel ideal sheaves pinned through the
inclusions into the two structure sheaves.  Then the comparison of inverse images of
[Stacks Project, Tag 03LU] together with `κ` on the left, and together with the étale-source
localisation of [Stacks Project, Tag 04CU] on the right, intertwine the first arrow of `i₀ ≫ ι`
with the first arrow of `i₀`.

This is the clause the reduction of [Stacks Project, Tag 04CE] of an immersion to a closed
immersion in an étale ambient space was missing.  It is
`AlgebraicGeometry.Space.kernelConormalFirstMap_comp` at the étale-source localisation, which has
the characterising property of [Stacks Project, Tag 04CX] for the square whose top edge is `ι`
and whose bottom edge is the identity. -/
theorem kernelConormalFirstMap_etaleAmbient (i₀ : Z ⟶ Amb) (ι : Amb ⟶ X)
    (hι : IsEtale B S hS ι.hom) (b : X ⟶ Bb)
    (κ : (modulePullback B S hS ι).obj
        (kernelIdealSheaf B S hS (i₀ ≫ ι)).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS i₀).toSheafOfModules)
    (hκ : κ ≫ (kernelIdealSheaf B S hS i₀).ι =
      (modulePullback B S hS ι).map (kernelIdealSheaf B S hS (i₀ ≫ ι)).ι ≫
        structureModulePullbackMap B S hS ι) :
    (modulePullbackCompIso B S hS i₀ ι).inv.app
          (kernelIdealSheaf B S hS (i₀ ≫ ι)).toSheafOfModules ≫
        (modulePullback B S hS i₀).map κ ≫ kernelConormalFirstMap B S hS i₀ (ι ≫ b) =
      kernelConormalFirstMap B S hS (i₀ ≫ ι) b ≫
        (modulePullbackCompIso B S hS i₀ ι).inv.app (sheafOfDifferentials B S hS b) ≫
          (modulePullback B S hS i₀).map (etaleSourceLocalizationHom B S hS ι hι b) :=
  kernelConormalFirstMap_comp B S hS i₀ ι b (ι ≫ b)
    (isSheafOfDifferentialsMap_etaleSourceLocalizationHom B S hS ι hι b) κ hκ

/-- **The comparison of the two first arrows across an étale change of ambient space, with no
hypothesis at all.**  `AlgebraicGeometry.Space.kernelConormalFirstMap_etaleAmbient` at the
canonical comparison `ι^*𝓘_{i₀ ≫ ι} ⟶ 𝓘_{i₀}` of the kernel ideal sheaves.

This is the clause the reduction of [Stacks Project, Tag 04CE] of an immersion to a closed
immersion in an étale ambient space was missing, with both of its comparisons the canonical
ones: the kernel ideal sheaves by [Stacks Project, Tag 09RS] in degree one, the sheaves of
differentials by [Stacks Project, Tag 03LU] and the étale-source localisation of
[Stacks Project, Tag 04CU]. -/
theorem kernelConormalFirstMap_etaleAmbient_compPullbackMap (i₀ : Z ⟶ Amb) (ι : Amb ⟶ X)
    (hι : IsEtale B S hS ι.hom) (b : X ⟶ Bb) :
    (modulePullbackCompIso B S hS i₀ ι).inv.app
          (kernelIdealSheaf B S hS (i₀ ≫ ι)).toSheafOfModules ≫
        (modulePullback B S hS i₀).map (kernelIdealCompPullbackMap B S hS i₀ ι) ≫
          kernelConormalFirstMap B S hS i₀ (ι ≫ b) =
      kernelConormalFirstMap B S hS (i₀ ≫ ι) b ≫
        (modulePullbackCompIso B S hS i₀ ι).inv.app (sheafOfDifferentials B S hS b) ≫
          (modulePullback B S hS i₀).map (etaleSourceLocalizationHom B S hS ι hι b) :=
  kernelConormalFirstMap_compPullbackMap B S hS i₀ ι b (ι ≫ b)
    (isSheafOfDifferentialsMap_etaleSourceLocalizationHom B S hS ι hι b)

end AlgebraicGeometry.Space

end
