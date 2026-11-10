module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.SubmoduleAscendingChain
public import StacksFrontier.AlgebraicGeometry.AffineExtend.Basic
public import StacksFrontier.AlgebraicGeometry.AffineSubsheaf.Generation
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SubQuotient
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.SubmoduleRestrict.Locality
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint

/-!
# Spreading a submodule of a stalk out to a coherent subsheaf

Let `X` be a scheme, `F` an `𝒪_X`-module, `x` a point of `X` and `P` an `𝒪_{X,x}`-submodule of
the stalk `F_x`. This file produces, for `X` affine and locally Noetherian and `F` coherent, a
*coherent* submodule `G ⊆ F` whose stalk at `x` is exactly `P`.

The stalk of a submodule `G ⊆ F` is described inside `F_x` as the submodule `stalkSubmodule G x`
of germs at `x` of the local sections of `G`; this avoids packaging `G` as a module and passing
to the stalk functor.

On a scheme that is merely locally Noetherian the same holds: an affine open containing the
point carries such a coherent subsheaf of the restriction of `F`, and [Stacks, Tag 01PE] extends
it to a quasi-coherent — hence coherent — submodule of `F` over the whole scheme, the inclusion
of an open of a locally Noetherian scheme being a quasi-compact morphism. The stalk is unchanged
by the extension because it is read off the sections over the opens inside that affine open.

The construction is the subsheaf cut out by a finite set `A` of global sections of `F`, whose
sections over an affine open are the span of the restrictions of `A`
(`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.spanRestrictSubsheaf`). Its stalk at `x` is the
`𝒪_{X,x}`-span of the germs of `A`, computed here for an arbitrary scheme: one direction shrinks
a local section to an affine open, where it is a combination of restrictions of `A`, and the
other direction is that each member of `A` is a global section of the subsheaf. On an affine
scheme every element of `F_x` becomes the germ of a global section after multiplication by a
function invertible at `x`, so a finite generating set of `P` can be replaced by germs of global
sections, and `A` is that set.

## Main definitions

* `Stacks.AlgebraicGeometry.StalkSpread.stalkSubmodule`: the stalk at `x` of a submodule of `F`,
  as an `𝒪_{X,x}`-submodule of `F_x`.
* `Stacks.AlgebraicGeometry.StalkSpread.restrictStalkSemilinear`: the stalk at a point of an open
  subscheme of the restriction of `F`, compared with the stalk of `F`, as a map of modules
  semilinear over the isomorphism of the stalks of the two structure sheaves.

## Main results

* `Stacks.AlgebraicGeometry.StalkSpread.stalkSubmodule_spanRestrictSubsheaf`: the stalk at `x`
  of the subsheaf cut out by a set `A` of global sections is the `𝒪_{X,x}`-span of the germs of
  `A` at `x`.
* `Stacks.AlgebraicGeometry.StalkSpread.exists_isCoherent_submodule_stalkSubmodule_eq`: on an
  affine locally Noetherian scheme, every finitely generated submodule of a stalk of a
  quasi-coherent module is the stalk of a coherent submodule.
* `StalkSpread.exists_isCoherent_submodule_stalkSubmodule_eq_of_isCoherent`: the same with the
  finite generation hypothesis discharged by coherence of `F`.
* `Stacks.AlgebraicGeometry.StalkSpread.stalkSubmodule_restrictTo`: the stalk of the restriction
  of a submodule to an open subscheme is the preimage of the stalk of that submodule under the
  comparison of the two stalks.
* `Stacks.AlgebraicGeometry.StalkSpread.exists_isQuasicoherent_submodule_restrictTo_eq`:
  [Stacks, Tag 01PE] in the form that prescribes an arbitrary submodule of the restriction of `F`
  to a quasi-compact open.
* `StalkSpread.exists_isCoherent_submodule_stalkSubmodule_eq_of_isLocallyNoetherian`: every
  submodule of a stalk of a coherent module on a *locally* Noetherian scheme — affineness of the
  scheme no longer assumed — is the stalk of a coherent submodule.

## Implementation notes

The `𝒪_{X,x}`-module structure on `F_x` is `Stacks.ModuleStalkSpecialization.stalkModule`, made a
local instance here; instance search does not find it on its own because it cannot unfold
`AlgebraicGeometry.Scheme.Modules.presheaf`.

A function invertible at `x` has invertible germ by `isUnit_germ_of_mem_primeCompl`, which reads
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` through
`IsLocalization.AtPrime.isUnit_to_map_iff`.

The point of the open subscheme at which the comparison of stalks is taken is introduced as a
variable, by `obtain ⟨y, rfl⟩ : ∃ y : V.toScheme, y.1 = x`, rather than written as the pair
`⟨x, hxV⟩`: the `𝒪_{V,y}`-module structure on the stalk of `F|_V` at `y` is found by instance
search for a variable `y` and not for that pair.

Monomorphy of the inclusion of a concrete submodule is passed positionally, as recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/AffineExtend/Basic.lean`: the instance
`Stacks.AlgebraicGeometry.Tag01PFAffineExtend.mono_submoduleι` is not found by the `[Mono f]`
binder of an imported lemma.

Each germ identity used in the construction of `stalkSubmodule` is named in a `have` before it is
rewritten: the implicit membership proofs produced by `TopCat.Presheaf.germ_res_apply` differ from
the ones in the goal, and only ascribing the identity to the shape the goal has makes the rewrite
fire.

## References

* [Stacks Project, Tag 01AR](https://stacks.math.columbia.edu/tag/01AR), the stalk of a
  generated subsheaf.
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF), the subsheaf cut out
  by a set of global sections.
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE), the extension of a
  quasi-coherent submodule from a quasi-compact open.
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ), coherence as
  quasi-coherence plus finite type.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.StalkSpread

attribute [local instance] Stacks.ModuleStalkSpecialization.stalkModule

variable {X : Scheme.{u}} {F : X.Modules}

/-- **The stalk at `x` of a submodule `G ⊆ F`**, as the `𝒪_{X,x}`-submodule of `F_x` of germs at
`x` of the local sections of `G`. -/
def stalkSubmodule (G : F.Submodule) (x : X) :
    Submodule (X.presheaf.stalk x) (F.presheaf.stalk x) where
  carrier := {t | ∃ (V : X.Opens) (hxV : x ∈ V) (a : Γ(F, V)),
    a ∈ G.obj (op V) ∧ F.presheaf.germ V x hxV a = t}
  zero_mem' := ⟨⊤, Set.mem_univ x, 0, (G.obj (op ⊤)).zero_mem, map_zero _⟩
  add_mem' := by
    rintro t₁ t₂ ⟨V, hxV, a, ha, rfl⟩ ⟨W, hxW, b, hb, rfl⟩
    have hxZ : x ∈ (V ⊓ W : X.Opens) := ⟨hxV, hxW⟩
    have h₁ : F.presheaf.germ (V ⊓ W) x hxZ
        (F.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op a)
        = F.presheaf.germ V x hxV a :=
      TopCat.Presheaf.germ_res_apply F.presheaf _ x hxZ a
    have h₂ : F.presheaf.germ (V ⊓ W) x hxZ
        (F.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op b)
        = F.presheaf.germ W x hxW b :=
      TopCat.Presheaf.germ_res_apply F.presheaf _ x hxZ b
    refine ⟨V ⊓ W, hxZ,
      F.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op a +
        F.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op b,
      add_mem (G.map_mem _ ha) (G.map_mem _ hb), ?_⟩
    rw [map_add, h₁, h₂]
  smul_mem' := by
    rintro r t ⟨V, hxV, a, ha, rfl⟩
    obtain ⟨W, hxW, c, hc⟩ := X.presheaf.exists_germ_eq r
    have hxZ : x ∈ (W ⊓ V : X.Opens) := ⟨hxW, hxV⟩
    have h₁ : X.presheaf.germ (W ⊓ V) x hxZ
        (X.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op c) = r :=
      (TopCat.Presheaf.germ_res_apply X.presheaf _ x hxZ c).trans hc
    have h₂ : F.presheaf.germ (W ⊓ V) x hxZ
        (F.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op a)
        = F.presheaf.germ V x hxV a :=
      TopCat.Presheaf.germ_res_apply F.presheaf _ x hxZ a
    refine ⟨W ⊓ V, hxZ,
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op c •
        F.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op a,
      Submodule.smul_mem _ _ (G.map_mem _ ha), ?_⟩
    rw [ModuleStalkSpecialization.germ_smul, h₁, h₂]

/-- An element of `F_x` lies in the stalk of `G` exactly when it is the germ at `x` of a local
section of `G`. -/
lemma mem_stalkSubmodule_iff (G : F.Submodule) (x : X) (t : F.presheaf.stalk x) :
    t ∈ stalkSubmodule G x ↔
      ∃ (V : X.Opens) (hxV : x ∈ V) (a : Γ(F, V)),
        a ∈ G.obj (op V) ∧ F.presheaf.germ V x hxV a = t :=
  Iff.rfl

/-- The germ at `x` of a local section of `G` lies in the stalk of `G`. -/
lemma germ_mem_stalkSubmodule {G : F.Submodule} {V : X.Opens} {x : X} (hxV : x ∈ V)
    {a : Γ(F, V)} (ha : a ∈ G.obj (op V)) :
    F.presheaf.germ V x hxV a ∈ stalkSubmodule G x :=
  ⟨V, hxV, a, ha, rfl⟩

/-- The germ of a restricted section is the germ of the section. -/
private theorem germ_map_homOfLE (F : X.Modules) {V W : X.Opens} (h : W ≤ V) {x : X}
    (hxW : x ∈ W) (a : Γ(F, V)) :
    F.presheaf.germ W x hxW (F.presheaf.map (homOfLE h).op a) = F.presheaf.germ V x (h hxW) a :=
  TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE h) x hxW a

/-- **A function not vanishing at a point of an affine open has invertible germ there.** This is
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` read through
`IsLocalization.AtPrime.isUnit_to_map_iff`. -/
lemma isUnit_germ_of_mem_primeCompl {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (c : Γ(X, U)) (hc : c ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) :
    IsUnit (X.presheaf.germ U x hx c) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal c).mpr hc

/-- **The stalk of the subsheaf cut out by a set of global sections.** For a quasi-coherent `F`
and a set `A` of global sections of `F`, the stalk at `x` of
`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.spanRestrictSubsheaf F A` is the
`𝒪_{X,x}`-submodule of `F_x` spanned by the germs at `x` of the members of `A`.

For the inclusion of the stalk in the span, a local section of the subsheaf is restricted to an
affine open containing `x` — the affine opens form a basis — where it is a `Γ(X, W)`-combination
of restrictions of `A`; germs are unchanged by restriction, and the germ map is semilinear over
the germ map of the structure sheaf, so the germ of such a combination lies in the span. For the
other inclusion, each member of `A` is a global section of the subsheaf, its restriction to any
affine open being one of the generators of the span there. -/
theorem stalkSubmodule_spanRestrictSubsheaf [F.IsQuasicoherent] (A : Set Γ(F, ⊤)) (x : X) :
    stalkSubmodule (Tag01PFAffineSubsheaf.spanRestrictSubsheaf F A) x =
      Submodule.span (X.presheaf.stalk x)
        ((fun a : Γ(F, ⊤) => F.presheaf.germ ⊤ x (Set.mem_univ x) a) '' A) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro t ⟨V, hxV, a, ha, rfl⟩
    obtain ⟨-, ⟨W, hWaff, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (V : Set X) from hxV) V.isOpen
    have hle : W ≤ V := hWV
    have key : ∀ y : Γ(F, W),
        y ∈ Submodule.span Γ(X, W) (Tag01PFAffineSubsheaf.spanRestrict F A ⟨W, hWaff⟩) →
          F.presheaf.germ W x hxW y ∈ Submodule.span (X.presheaf.stalk x)
            ((fun a : Γ(F, ⊤) => F.presheaf.germ ⊤ x (Set.mem_univ x) a) '' A) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a₀, ha₀, rfl⟩ := hy
        rw [germ_map_homOfLE]
        exact Submodule.subset_span ⟨a₀, ha₀, rfl⟩
      | zero => simpa only [map_zero] using Submodule.zero_mem _
      | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        rw [ModuleStalkSpecialization.germ_smul]
        exact Submodule.smul_mem _ _ hy
    have haW : F.presheaf.map (homOfLE hle).op a ∈
        Tag01PFAffineSubsheaf.spanRestrictFamily F A ⟨W, hWaff⟩ := by
      rw [← Tag01PFAffineSubsheaf.obj_spanRestrictSubsheaf F A ⟨W, hWaff⟩]
      exact (Tag01PFAffineSubsheaf.spanRestrictSubsheaf F A).map_mem (homOfLE hle).op ha
    rw [← germ_map_homOfLE F hle hxW a]
    exact key _ haW
  · rintro y ⟨a, haA, rfl⟩
    exact germ_mem_stalkSubmodule (Set.mem_univ x) fun W _ => Submodule.subset_span ⟨a, haA, rfl⟩

/-- **Spreading a finitely generated submodule of a stalk out to a coherent subsheaf.** On an
affine locally Noetherian scheme, a finitely generated `𝒪_{X,x}`-submodule `P` of the stalk at
`x` of a quasi-coherent module `F` is the stalk at `x` of a coherent submodule of `F`.

Each generator of `P` becomes the germ of a global section of `F` after multiplication by a
function invertible at `x`, so `P` is spanned by the germs of a finite set `A` of global
sections; the subsheaf cut out by `A` is coherent, being quasi-coherent of finite type on a
locally Noetherian scheme, and its stalk at `x` is that span. -/
theorem exists_isCoherent_submodule_stalkSubmodule_eq [IsAffine X] [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (P : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) (hP : P.FG) :
    ∃ G : F.Submodule, _root_.SheafOfModules.IsCoherent G.toSheafOfModules ∧
      stalkSubmodule G x = P := by
  classical
  obtain ⟨T, hT⟩ := hP
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  choose s c hc hsc using fun t : (↥T) =>
    ModuleStalkSpecialization.exists_germ_smul_eq_germ F hU (Set.mem_univ x)
      (t : F.presheaf.stalk x)
  refine ⟨Tag01PFAffineSubsheaf.spanRestrictSubsheaf F (Set.range s),
    Tag01PFAffineSubsheaf.isCoherent_spanRestrictModule F (Set.finite_range s), ?_⟩
  rw [stalkSubmodule_spanRestrictSubsheaf]
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro y ⟨a, ⟨t, rfl⟩, rfl⟩
    have hmem : F.presheaf.germ ⊤ x (Set.mem_univ x) (s t) ∈ P := by
      rw [← hsc t]
      refine P.smul_mem _ ?_
      rw [← hT]
      exact Submodule.subset_span t.2
    exact hmem
  · rw [← hT]
    refine Submodule.span_le.2 fun y hy => ?_
    obtain ⟨b, hb⟩ := (isUnit_germ_of_mem_primeCompl hU (Set.mem_univ x) (c ⟨y, hy⟩)
      (hc ⟨y, hy⟩)).exists_left_inv
    have hy' : y = b • F.presheaf.germ ⊤ x (Set.mem_univ x) (s ⟨y, hy⟩) := by
      rw [← hsc ⟨y, hy⟩, smul_smul, hb, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨s ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩)

/-- **Spreading a submodule of a stalk of a coherent module out to a coherent subsheaf.** On an
affine locally Noetherian scheme, *every* `𝒪_{X,x}`-submodule of the stalk at `x` of a coherent
module `F` is the stalk at `x` of a coherent submodule of `F`.

The stalk of a coherent module is a finite module over the local ring at the point, which is
Noetherian, so every submodule of the stalk is finitely generated. -/
theorem exists_isCoherent_submodule_stalkSubmodule_eq_of_isCoherent [IsAffine X]
    [IsLocallyNoetherian X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (x : X)
    (P : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    ∃ G : F.Submodule, _root_.SheafOfModules.IsCoherent G.toSheafOfModules ∧
      stalkSubmodule G x = P := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    Scheme.Modules.finite_stalk_of_isCoherent F x
  exact exists_isCoherent_submodule_stalkSubmodule_eq F x P (IsNoetherian.noetherian P)

/-! ### The comparison of a stalk on an open subscheme with a stalk on the scheme -/

/-- **The stalk of the restriction of an `𝒪_X`-module to an open subscheme, compared with the
stalk of the module.** For `V` an open of `X` and `x` a point of `V`, the comparison
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` identifies the stalk of `F|_V` at `x` with
the stalk of `F` at the image of `x`; this is that identification read as a map of modules,
semilinear over the ring isomorphism `AlgebraicGeometry.Scheme.Opens.stalkIso` of the stalks of
the two structure sheaves.

Semilinearity is checked on germs: every element of either stalk is a germ, the germ of a
product is the product of the germs by `Stacks.ModuleStalkSpecialization.germ_smul`, and the two
comparisons carry germs to germs. The two scalar actions on the sections of `F|_V` over an open
of `V` differ by `(V.ι.appIso _).inv`, which for the inclusion of an open subscheme is the
identity. -/
def restrictStalkSemilinear (V : X.Opens) (F : X.Modules) (x : V.toScheme) :
    ((F.restrict V.ι).presheaf.stalk x) →ₛₗ[(V.stalkIso x).hom.hom]
      (F.presheaf.stalk x.1) := by
  let e : (F.restrict V.ι).presheaf.stalk x ≅ F.presheaf.stalk x.1 :=
    (Scheme.Modules.restrictStalkNatIso V.ι x).app F
  refine { e.hom.hom with map_smul' := ?_ }
  intro r m
  obtain ⟨W₁, hxW₁, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq V.toScheme.presheaf r
  obtain ⟨W₂, hxW₂, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (F.restrict V.ι).presheaf m
  have hxZ : x ∈ (W₁ ⊓ W₂ : V.toScheme.Opens) := ⟨hxW₁, hxW₂⟩
  rw [← TopCat.Presheaf.germ_res_apply V.toScheme.presheaf
        (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) x hxZ a,
    ← TopCat.Presheaf.germ_res_apply (F.restrict V.ι).presheaf
        (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) x hxZ s]
  set a' := V.toScheme.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op a
  set s' := (F.restrict V.ι).presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op s
  change e.hom (V.toScheme.presheaf.germ (W₁ ⊓ W₂) x hxZ a' •
      (F.restrict V.ι).presheaf.germ (W₁ ⊓ W₂) x hxZ s') =
    (V.stalkIso x).hom (V.toScheme.presheaf.germ (W₁ ⊓ W₂) x hxZ a') •
      e.hom ((F.restrict V.ι).presheaf.germ (W₁ ⊓ W₂) x hxZ s')
  rw [← ModuleStalkSpecialization.germ_smul (F.restrict V.ι) hxZ a' s']
  have he : ∀ t : Γ(F.restrict V.ι, W₁ ⊓ W₂),
      e.hom ((F.restrict V.ι).presheaf.germ (W₁ ⊓ W₂) x hxZ t) =
        F.presheaf.germ (V.ι ''ᵁ (W₁ ⊓ W₂)) x.1 ⟨x, hxZ, rfl⟩ t := fun t =>
    ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app V.ι x F hxZ) t
  rw [he, he]
  have hr : (V.stalkIso x).hom (V.toScheme.presheaf.germ (W₁ ⊓ W₂) x hxZ a') =
      X.presheaf.germ (V.ι ''ᵁ (W₁ ⊓ W₂)) x.1 ⟨x, hxZ, rfl⟩ a' :=
    ConcreteCategory.congr_hom (V.germ_stalkIso_hom x hxZ) a'
  rw [hr]
  refine Eq.trans ?_ (ModuleStalkSpecialization.germ_smul F
    (show x.1 ∈ V.ι ''ᵁ (W₁ ⊓ W₂) from ⟨x, hxZ, rfl⟩) a' s')
  congr 1
  have h := ConcreteCategory.congr_hom
    (Scheme.Modules.smul_restrictAppIso_hom V.ι F (W₁ ⊓ W₂) a') s'
  change ((F.restrict V.ι).smul a').asHom s' = (F.smul a').asHom s'
  change ((F.restrict V.ι).smul a').asHom s' =
    (F.smul ((V.ι.appIso (W₁ ⊓ W₂)).inv a')).asHom s' at h
  have ha : (V.ι.appIso (W₁ ⊓ W₂)).inv a' = a' := by
    rw [Scheme.Opens.ι_appIso]
    exact CommRingCat.id_apply _ _
  rwa [ha] at h

/-- **The comparison carries the germ at `x` of a section of `F|_V` over an open `W` of `V` to
the germ at the image of `x` of that same section, read over the image open.** -/
theorem restrictStalkSemilinear_germ (V : X.Opens) (F : X.Modules) (x : V.toScheme)
    {W : V.toScheme.Opens} (hx : x ∈ W) (s : Γ(F.restrict V.ι, W)) :
    restrictStalkSemilinear V F x ((F.restrict V.ι).presheaf.germ W x hx s) =
      F.presheaf.germ (V.ι ''ᵁ W) x.1 ⟨x, hx, rfl⟩ s :=
  ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app V.ι x F hx) s

/-- **The comparison is bijective**, being the underlying map of an isomorphism of abelian
groups. -/
theorem bijective_restrictStalkSemilinear (V : X.Opens) (F : X.Modules) (x : V.toScheme) :
    Function.Bijective (restrictStalkSemilinear V F x) :=
  (ConcreteCategory.isIso_iff_bijective
    ((Scheme.Modules.restrictStalkNatIso V.ι x).app F).hom).1 (Iso.isIso_hom _)

/-! ### The stalk of a restricted submodule -/

/-- **An element of a stalk of `F|_V` lies in the stalk of the restriction of a submodule `N` of
`F` exactly when its image under the comparison lies in the stalk of `N`.**

An element of the stalk of `restrictTo V.ι N` at `x` is the germ of a section of `N` over an
image open, hence has image in the stalk of `N`. Conversely a section of `N` over an open `W` of
`X` whose germ at `x` is the image of `t` restricts to a section of `N` over `V ⊓ W`, which is
the image of an open of `V`; the germ there of that restriction has the same image as `t`, and
the comparison is injective. -/
theorem mem_stalkSubmodule_restrictTo_iff (V : X.Opens) {F : X.Modules} (N : F.Submodule)
    (x : V.toScheme) (t : (F.restrict V.ι).presheaf.stalk x) :
    t ∈ stalkSubmodule (SubmoduleRestrict.restrictTo V.ι N) x ↔
      restrictStalkSemilinear V F x t ∈ stalkSubmodule N x.1 := by
  constructor
  · rintro ⟨W, hxW, a, ha, rfl⟩
    rw [restrictStalkSemilinear_germ]
    exact germ_mem_stalkSubmodule (G := N) _
      ((SubmoduleRestrict.mem_restrictTo V.ι N a).1 ha)
  · rintro ⟨W, hxW, b, hb, hgerm⟩
    let W' : V.toScheme.Opens := V.ι ⁻¹ᵁ W
    have hxW' : x ∈ W' := hxW
    have hle : (V.ι ''ᵁ W') ≤ W := V.ι.image_preimage_le W
    let a : Γ(F.restrict V.ι, W') := F.presheaf.map (homOfLE hle).op b
    have ha : a ∈ (SubmoduleRestrict.restrictTo V.ι N).obj (op W') :=
      (SubmoduleRestrict.mem_restrictTo V.ι N a).2 (N.map_mem (homOfLE hle).op hb)
    have hkey : (F.restrict V.ι).presheaf.germ W' x hxW' a = t := by
      refine (bijective_restrictStalkSemilinear V F x).1 ?_
      rw [restrictStalkSemilinear_germ V F x hxW' a, ← hgerm]
      exact germ_map_homOfLE F hle ⟨x, hxW', rfl⟩ b
    exact hkey ▸ germ_mem_stalkSubmodule hxW' ha

/-- **The stalk of the restriction of a submodule to an open subscheme** is the preimage, under
the comparison of the two stalks, of the stalk of the submodule. -/
theorem stalkSubmodule_restrictTo (V : X.Opens) {F : X.Modules} (N : F.Submodule)
    (x : V.toScheme) :
    stalkSubmodule (SubmoduleRestrict.restrictTo V.ι N) x =
      Submodule.comap (restrictStalkSemilinear V F x) (stalkSubmodule N x.1) :=
  SetLike.ext fun t => mem_stalkSubmodule_restrictTo_iff V N x t

/-! ### Spreading out from an affine open -/

open Stacks.AlgebraicGeometry.SubmodulePrimitives Stacks.AlgebraicGeometry.SubmoduleRestrict

open Stacks.AlgebraicGeometry.Tag01PFAffineExtend in
/-- **[Stacks, Tag 01PE] prescribing a submodule of the restriction.** A quasi-coherent submodule
of the restriction of a quasi-coherent module `F` to a quasi-compact open `W` is the restriction
of a quasi-coherent submodule of `F`.

This is the variant of
`Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_isQuasicoherent_submodule_restrictTo_eq`
whose prescribed submodule is an arbitrary submodule of `F|_W` instead of the restriction of a
submodule of `F`; the proof is the same, the hypothesis on the submodule never being used. The
passage between the concrete and the categorical spelling of a submodule is
`SheafOfModules.Submodule.toSubobject` and
`Stacks.AlgebraicGeometry.SubmodulePrimitives.ofSubobject`. -/
theorem exists_isQuasicoherent_submodule_restrictTo_eq {F : X.Modules} [F.IsQuasicoherent]
    {W : X.Opens} (hqcW : QuasiCompact W.ι) (G₀ : (F.restrict W.ι).Submodule)
    (hqc : (G₀.toSheafOfModules : W.toScheme.Modules).IsQuasicoherent) :
    ∃ M : F.Submodule, (M.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      restrictTo W.ι M = G₀ := by
  obtain ⟨H, hHqc, e, he⟩ := AlgebraicGeometry.exists_quasicoherentSubobject_restrict W.ι F
    (G₀.toSubobject)
    (SubmoduleRelativeLocality.isQuasicoherent_of_iso (toSubobjectIso G₀).symm hqc)
  refine ⟨ofSubobject H,
    SubmoduleRelativeLocality.isQuasicoherent_of_iso (ofSubobjectIso H) hHqc, ?_⟩
  have hassoc : (e ≪≫ toSubobjectIso G₀).hom ≫ submoduleι G₀ =
      e.hom ≫ (toSubobjectIso G₀).hom ≫ submoduleι G₀ := Category.assoc _ _ _
  have he₂ : (e ≪≫ toSubobjectIso G₀).hom ≫ submoduleι G₀ =
      (Scheme.Modules.restrictFunctor W.ι).map H.arrow := by
    rwa [hassoc, toSubobjectIso_hom_comp]
  have hmonoiso : Mono (e ≪≫ toSubobjectIso G₀).hom :=
    @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom (e ≪≫ toSubobjectIso G₀))
  have hmono : Mono ((Scheme.Modules.restrictFunctor W.ι).map H.arrow) := by
    rw [← he₂]
    exact @mono_comp _ _ _ _ _ _ hmonoiso _ (mono_submoduleι _)
  exact (@restrictTo_ofHom_eq_of_iso _ _ _ W.ι _ _ _ H.arrow (submoduleι G₀)
    (mono_submoduleι _) hmono _ he₂).trans (ofHom_submoduleι _)

/-- **Spreading a submodule of a stalk of a coherent module out to a coherent subsheaf, on a
locally Noetherian scheme.** Every `𝒪_{X,x}`-submodule of the stalk at `x` of a coherent module
`F` on a locally Noetherian scheme is the stalk at `x` of a coherent submodule of `F`.

An affine open `V` containing `x` is chosen from the basis of affine opens. The restriction of
`F` to `V` is coherent, `V` is affine and locally Noetherian, so
`Stacks.AlgebraicGeometry.StalkSpread.exists_isCoherent_submodule_stalkSubmodule_eq_of_isCoherent`
produces a coherent submodule of `F|_V` whose stalk at `x` is the preimage of the given submodule
under the comparison of the two stalks. The inclusion of an open of a locally Noetherian scheme
is a quasi-compact morphism, so [Stacks, Tag 01PE] extends that submodule to a quasi-coherent
submodule of `F` restricting to it; a quasi-coherent submodule of a coherent module on a locally
Noetherian scheme is coherent, and its stalk at `x` is the given submodule because the comparison
is bijective. -/
theorem exists_isCoherent_submodule_stalkSubmodule_eq_of_isLocallyNoetherian
    [IsLocallyNoetherian X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (x : X)
    (P : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    ∃ G : F.Submodule, _root_.SheafOfModules.IsCoherent G.toSheafOfModules ∧
      stalkSubmodule G x = P := by
  obtain ⟨V, hVaff, hxV⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    obtain ⟨-, ⟨W, hWaff, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨W, hWaff, hxW⟩
  obtain ⟨y, rfl⟩ : ∃ y : V.toScheme, y.1 = x := ⟨⟨x, hxV⟩, rfl⟩
  have : IsAffine V.toScheme := hVaff
  have : (F.restrict V.ι).IsCoherent := AlgebraicGeometry.Modules.isCoherent_restrict F V
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨G₀, hG₀coh, hG₀⟩ :=
    exists_isCoherent_submodule_stalkSubmodule_eq_of_isCoherent (F.restrict V.ι) y
      (Submodule.comap (restrictStalkSemilinear V F y) P)
  obtain ⟨M, hMqc, hM⟩ := exists_isQuasicoherent_submodule_restrictTo_eq
    inferInstance G₀ (isQuasicoherent_of_isCoherent _)
  have hMc : _root_.SheafOfModules.IsCoherent (M.toSheafOfModules : X.Modules) :=
    @Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent X _ F
      (M.toSheafOfModules : X.Modules) ‹F.IsCoherent› hMqc
      (Stacks.AlgebraicGeometry.Tag01PFAffineExtend.submoduleι M)
      (Stacks.AlgebraicGeometry.Tag01PFAffineExtend.mono_submoduleι M)
  refine ⟨M, hMc, ?_⟩
  have h := stalkSubmodule_restrictTo V M y
  rw [hM, hG₀] at h
  refine SetLike.ext fun t => ?_
  obtain ⟨u, rfl⟩ := (bijective_restrictStalkSemilinear V F y).2 t
  exact (SetLike.ext_iff.1 h u).symm

end Stacks.AlgebraicGeometry.StalkSpread

end
