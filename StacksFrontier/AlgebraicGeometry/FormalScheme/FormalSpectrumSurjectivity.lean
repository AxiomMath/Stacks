module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumGlobalSectionsIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison map of Stacks 0AHZ is a bijection

For admissible topological rings `A` and `B` the map taking a continuous ring homomorphism
`A → B` to the induced morphism `Spf B → Spf A` of locally topologically ringed spaces is a
bijection
`Hom_cont(A, B) = Mor_{LTRS}((Spf B, 𝒪_{Spf B}), (Spf A, 𝒪_{Spf A}))`.
Injectivity is `AlgebraicGeometry.injective_spfLTRSMap`; this module proves surjectivity and
assembles the two halves.

The candidate preimage of a morphism `g : Spf B → Spf A` is the homomorphism
`AlgebraicGeometry.ltrsGlobalSectionsRingHom` that `g` induces on global sections, read through
the identifications `Γ(Spf A, 𝒪_{Spf A}) = A` and `Γ(Spf B, 𝒪_{Spf B}) = B` of Stacks 0AHY. By
`AlgebraicGeometry.exists_ltrsGlobalSectionsMap_eq_and_base_eq` the morphism attached to it
already agrees with `g` on global sections and on underlying topological spaces. What is proved
here is that this forces the two comparison maps of sheaves to agree at *every* open, which is
the last step of the identification.

## Main definitions

* `AlgebraicGeometry.spfAwayResidueOn`: the residue of a section of `𝒪_{Spf A}` over a basic open
  `D(f) ∩ Spf A` in the sections of the term `𝒪_I` of the inverse system there, a ring that is
  the localization `(A/I)_f`.
* `AlgebraicGeometry.spfLTRSEquiv`: the bijection of Stacks 0AHZ as an equivalence of types.

## Main results

* `AlgebraicGeometry.isBasis_spfBasicOpen`: the basic opens `D(f) ∩ Spf A` form a basis of the
  topology of `Spf A`.
* `AlgebraicGeometry.spfPresheafOn_spfBasicOpen_hom_ext`: **a continuous homomorphism from the
  sections of `𝒪_{Spf A}` over a basic open into a discrete ring is determined by its values on
  the restrictions of global sections.**
* `AlgebraicGeometry.spfPresheaf_pushforward_hom_ext`: two maps `𝒪_{Spf A} → b_* 𝒪_{Spf B}` of
  presheaves of topological rings along a continuous map `b : Spf B → Spf A` that pulls basic
  opens back to quasi-compact opens agree as soon as they agree on global sections.
* `AlgebraicGeometry.surjective_spfLTRSMap` is the surjectivity half of Stacks 0AHZ, and
  `AlgebraicGeometry.bijective_spfLTRSMap` together with `AlgebraicGeometry.spfLTRSEquiv` is the
  full bijection.

## Implementation notes

The reduction to the basic opens is free: the basic opens form a basis of `Spf A`, the target
`b_* 𝒪_{Spf B}` is the pushforward of a sheaf and hence a sheaf, and a map of presheaves into a
sheaf is determined by its components on a basis (`CategoryTheory.TopCat.Sheaf.hom_ext`).

Over a *single* basic open `D(a) ∩ Spf A` the two maps are compared after projecting the target
`𝒪_{Spf B} = lim 𝒪^B_J` onto one term `𝒪^B_J`, whose sections over the preimage of
`D(a) ∩ Spf A` are discrete because that preimage is quasi-compact. Both projected maps are
therefore continuous homomorphisms into a discrete ring, and
`AlgebraicGeometry.exists_isIdealOfDefinition_forall_app_eq_zero` applied to the *pair* of them —
a family indexed by `Bool` — makes both factor through the sections of one and the same term
`𝒪^A_I` over `D(a) ∩ Spf A`. The uniformity that is needed is uniformity over the two maps at one
open, not over a basis of opens: the latter is not available, the basis being infinite.

Those sections are the localization `(A/I)_{\bar a}` by
`AlgebraicGeometry.isLocalization_spfComponentOn_spfBasicOpen`, so for a section `s` there is `n`
and `x : A` with `\bar a^n \cdot s` and `x` having the same residue; the restriction of `a` to
`D(a) ∩ Spf A` has invertible residue in every term, hence is invertible; and the two maps agree
on restrictions of global sections by naturality. Those three facts force them to agree on `s`.

No completeness of `A` or `B` enters either of the two extensionality statements: they hold for
pre-admissible rings. Admissibility is used only to produce the candidate preimage, through
Stacks 0AHY.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

open TopologicalRing

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-! ### The basic opens form a basis -/

omit [IsTopologicalRing A] in
/-- The opens `D(f) ∩ Spf A` form a basis of the topology of the formal spectrum: they are the
traces on the open primes of the basic opens of `Spec A`, which form a basis there. -/
theorem isBasis_spfBasicOpen : Opens.IsBasis (Set.range (spfBasicOpen A)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨W, hWopen, hWU⟩ := isOpen_induced_iff.1 U.2
  obtain ⟨s, ⟨f, rfl⟩, hxs, hsW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show x.1 ∈ W from hWU.symm.subset hx) hWopen
  exact ⟨spfBasicOpen A f, ⟨f, rfl⟩, hxs, fun y hy => hWU.subset (hsW hy)⟩

/-! ### The residue of a section over a basic open -/

/-- The residue of a section of `𝒪_{Spf A}` over the basic open `D(f) ∩ Spf A` in the sections of
the term `𝒪_I` of the inverse system there: the projection of `𝒪_{Spf A} = lim 𝒪_λ` onto `𝒪_I`,
read as a map of rings into `Γ(D(f) ∩ Spf A, 𝒪_I) = (A/I)_f`.

The projection itself is a map of topological rings into the pseudo-discretisation of `𝒪_I`; the
point of this name is to spell its target as the ring of sections of `𝒪_I`, which is where the
`A/I`-algebra structure and the localization instance live. -/
noncomputable def spfAwayResidueOn (I : SpfIndex A P) (f : A) :
    ((spfPresheafOn A P).obj (op (spfBasicOpen A f))).α →+*
      (spfComponentOn A I).obj (op (spfBasicOpen A f)) :=
  ((spfProjectionOn A I).app (op (spfBasicOpen A f))).1

/-- The residue of a section of `𝒪_{Spf A}` over the basic open `D(f) ∩ Spf A` in the sections of
the term `𝒪_I` of the inverse system there: the projection of `𝒪_{Spf A} = lim 𝒪_λ` onto `𝒪_I`,
read as a map of rings into `Γ(D(f) ∩ Spf A, 𝒪_I) = (A/I)_f`.

The projection itself is a map of topological rings into the pseudo-discretisation of `𝒪_I`; the
point of this name is to spell its target as the ring of sections of `𝒪_I`, which is where the
`A/I`-algebra structure and the localization instance live.

The ideals-of-definition case of `spfAwayResidueOn`. -/
@[reducible] noncomputable def spfAwayResidue (I : IdealsOfDefinition A) (f : A) :
    ((spfPresheaf A).obj (op (spfBasicOpen A f))).α →+*
      (spfComponent A I).obj (op (spfBasicOpen A f)) :=
  spfAwayResidueOn (A := A) (P := IsIdealOfDefinition) (I := I) (f := f)

/-- The residue over a basic open is the projection of `𝒪_{Spf A}` onto the term `𝒪_I`. -/
theorem spfAwayResidueOn_apply (I : SpfIndex A P) (f : A)
    (s : ((spfPresheafOn A P).obj (op (spfBasicOpen A f))).α) :
    spfAwayResidueOn A I f s = ((spfProjectionOn A I).app (op (spfBasicOpen A f))).1 s := rfl

/-- The residue over a basic open is the projection of `𝒪_{Spf A}` onto the term `𝒪_I`.

The ideals-of-definition case of `spfAwayResidueOn_apply`. -/
theorem spfAwayResidue_apply (I : IdealsOfDefinition A) (f : A)
    (s : ((spfPresheaf A).obj (op (spfBasicOpen A f))).α) :
    spfAwayResidue A I f s = ((spfProjection A I).app (op (spfBasicOpen A f))).1 s :=
  spfAwayResidueOn_apply (A := A) (P := IsIdealOfDefinition) (I := I) (f := f) (s := s)

/-- A morphism of functors into `TopCommRingCat` commutes with the maps of the functors,
elementwise. -/
private theorem app_map_apply {C : Type*} [Category C] {F G : C ⥤ TopCommRingCat.{u}} (d : F ⟶ G)
    {X Y : C} (i : X ⟶ Y) (t : (F.obj X).α) :
    (d.app Y).1 ((F.map i).1 t) = (G.map i).1 ((d.app X).1 t) :=
  congrArg (fun k : F.obj X ⟶ G.obj Y => k.1 t) (d.naturality i)

/-- The residue over `D(f) ∩ Spf A` of the restriction of the global section attached to `c : A`
is the image of `c` in `A/I` read into `(A/I)_f`.

Both steps are already available: the projection of the canonical map `A → Γ(Spf A, 𝒪_{Spf A})`
onto the term `𝒪_I` is the component `A → A/I ≅ Γ(Spec (A/I), 𝒪)`, and restricting a section
coming from `A/I` to a smaller open leaves it coming from `A/I`. -/
theorem spfAwayResidueOn_restrict_spfGammaHomOn (I : SpfIndex A P) (f c : A) :
    spfAwayResidueOn A I f
        (((spfPresheafOn A P).map (homOfLE (le_top : spfBasicOpen A f ≤ ⊤)).op).1
          ((spfGammaHomOn A P).1 c))
      = algebraMap (A ⧸ I.1) ((spfComponentOn A I).obj (op (spfBasicOpen A f)))
          (Ideal.Quotient.mk I.1 c) := by
  have hnat := app_map_apply (spfProjectionOn A I) (homOfLE (le_top : spfBasicOpen A f ≤ ⊤)).op
    ((spfGammaHomOn A P).1 c)
  have hcomp : ((spfProjectionOn A I).app (op ⊤)).1 ((spfGammaHomOn A P).1 c)
      = (spfGammaComponentHomOn A I).hom c :=
    congrArg
      (fun k : TopCommRingCat.of A ⟶ (pseudoDiscrete (spfComponentOn A I)).obj (op ⊤) => k.1 c)
      (spfGammaHomOn_comp_spfProjection_app_top A I)
  refine hnat.trans ((congrArg ((pseudoDiscrete (spfComponentOn A I)).map
    (homOfLE (le_top : spfBasicOpen A f ≤ ⊤)).op).1 hcomp).trans ?_)
  rfl

/-- The residue over `D(f) ∩ Spf A` of the restriction of the global section attached to `c : A`
is the image of `c` in `A/I` read into `(A/I)_f`.

Both steps are already available: the projection of the canonical map `A → Γ(Spf A, 𝒪_{Spf A})`
onto the term `𝒪_I` is the component `A → A/I ≅ Γ(Spec (A/I), 𝒪)`, and restricting a section
coming from `A/I` to a smaller open leaves it coming from `A/I`.

The ideals-of-definition case of `spfAwayResidueOn_restrict_spfGammaHomOn`. -/
theorem spfAwayResidue_restrict_spfGammaHom (I : IdealsOfDefinition A) (f c : A) :
    spfAwayResidue A I f
        (((spfPresheaf A).map (homOfLE (le_top : spfBasicOpen A f ≤ ⊤)).op).1
          ((spfGammaHom A).1 c))
      = algebraMap (A ⧸ I.1) ((spfComponent A I).obj (op (spfBasicOpen A f)))
          (Ideal.Quotient.mk I.1 c) :=
  spfAwayResidueOn_restrict_spfGammaHomOn (A := A) (P := IsIdealOfDefinition) (I := I) (f := f)
    (c := c)

/-- The restriction to `D(f) ∩ Spf A` of the global section of `𝒪_{Spf A}` attached to `f` is
invertible: its residue in each term `𝒪_I` of the inverse system is the image of `f` in the
localization `(A/I)_f`, which is a unit there, and a section of a limit of topological rings
whose components are all units is a unit. -/
theorem isUnit_restrict_spfGammaHomOn_self (f : A) :
    IsUnit (((spfPresheafOn A P).map (homOfLE (le_top : spfBasicOpen A f ≤ ⊤)).op).1
      ((spfGammaHomOn A P).1 f)) := by
  refine TopCommRingCat.isUnit_of_isLimit
    (spfObjIsLimitOn A P (spfBasicOpen A f)) _ fun I => ?_
  have hunit : IsUnit (spfAwayResidueOn A I f
      (((spfPresheafOn A P).map (homOfLE (le_top : spfBasicOpen A f ≤ ⊤)).op).1
        ((spfGammaHomOn A P).1 f))) := by
    rw [spfAwayResidueOn_restrict_spfGammaHomOn A I f f]
    exact IsLocalization.map_units _ ⟨Ideal.Quotient.mk I.1 f, Submonoid.mem_powers _⟩
  exact hunit

/-- The restriction to `D(f) ∩ Spf A` of the global section of `𝒪_{Spf A}` attached to `f` is
invertible: its residue in each term `𝒪_I` of the inverse system is the image of `f` in the
localization `(A/I)_f`, which is a unit there, and a section of a limit of topological rings
whose components are all units is a unit.

The ideals-of-definition case of `isUnit_restrict_spfGammaHomOn_self`. -/
theorem isUnit_restrict_spfGammaHom_self (f : A) :
    IsUnit (((spfPresheaf A).map (homOfLE (le_top : spfBasicOpen A f ≤ ⊤)).op).1
      ((spfGammaHom A).1 f)) :=
  isUnit_restrict_spfGammaHomOn_self (A := A) (P := IsIdealOfDefinition) (f := f)

/-! ### Sections over a basic open are generated by the global sections -/

/-- **A continuous homomorphism out of the sections over a basic open is determined by the global
sections.** Two continuous ring homomorphisms from `Γ(D(a) ∩ Spf A, 𝒪_{Spf A})` into a discrete
topological ring that agree on the restrictions of global sections are equal.

The two maps are a finite family of continuous homomorphisms into discrete rings, so by
`AlgebraicGeometry.exists_spfIndex_forall_app_eq_zero` one member `I` of the system
serves both: each of them kills every section whose residue in `𝒪_I` vanishes. The sections of
`𝒪_I` over `D(a) ∩ Spf A` are the localization `(A/I)_{\bar a}`, so for a section `s` there are
`n` and `x : A` such that `a^n · s` and `x` have the same residue, where `a` and `x` stand for
the restrictions of the global sections they define. Both maps therefore send `a^n · s` to the
image of `x`, they agree on the images of `a` and of `x` by hypothesis, and the image of `a` is
invertible because `a` is invertible on `D(a) ∩ Spf A`. Cancelling that unit identifies the two
values at `s`. -/
theorem spfPresheafOn_spfBasicOpen_hom_ext {T : TopCommRingCat.{u}} [DiscreteTopology T.α]
    (I₀ : SpfIndex A P) (a : A)
    {u v : (spfPresheafOn A P).obj (op (spfBasicOpen A a)) ⟶ T}
    (h : ∀ t : ((spfPresheafOn A P).obj (op ⊤)).α,
      u.1 (((spfPresheafOn A P).map (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op).1 t)
        = v.1 (((spfPresheafOn A P).map (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op).1 t)) :
    u = v := by
  classical
  obtain ⟨I, hker⟩ := exists_spfIndex_forall_app_eq_zero A I₀
    (fun _ : Bool => spfBasicOpen A a)
    (fun _ => isCompact_spfBasicOpen_of_isWeaklyPreAdmissible A
      (isWeaklyPreAdmissible_of_spfIndex A I₀) a)
    (fun _ => T) (fun i => cond i u v)
  refine Subtype.ext (RingHom.ext fun s => ?_)
  obtain ⟨p, hp⟩ := IsLocalization.surj (M := Submonoid.powers (Ideal.Quotient.mk I.1 a))
    (spfAwayResidueOn A I a s)
  obtain ⟨n, hn⟩ := p.2.2
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := I.1) p.1
  set ea := ((spfPresheafOn A P).map (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op).1
    ((spfGammaHomOn A P).1 a) with hea
  set ex := ((spfPresheafOn A P).map (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op).1
    ((spfGammaHomOn A P).1 x) with hex
  have hzero : spfAwayResidueOn A I a (ea ^ n * s - ex) = 0 := by
    rw [map_sub, map_mul, map_pow, hea, hex, spfAwayResidueOn_restrict_spfGammaHomOn A I a a,
      spfAwayResidueOn_restrict_spfGammaHomOn A I a x, hx, ← map_pow,
      show (Ideal.Quotient.mk I.1 a) ^ n = (p.2 : A ⧸ I.1) from hn, mul_comm, hp, sub_self]
  have hu := hker true _ hzero
  have hv := hker false _ hzero
  simp only [Bool.cond_true, Bool.cond_false, map_sub, map_mul, map_pow, sub_eq_zero] at hu hv
  have hua : u.1 ea = v.1 ea := h ((spfGammaHomOn A P).1 a)
  have hux : u.1 ex = v.1 ex := h ((spfGammaHomOn A P).1 x)
  have hunit : IsUnit (u.1 ea) := RingHom.isUnit_map _ (isUnit_restrict_spfGammaHomOn_self A a)
  refine (hunit.pow n).mul_left_cancel ?_
  rw [hu, hux, ← hv, hua]

/-- **A continuous homomorphism out of the sections over a basic open is determined by the global
sections.** Two continuous ring homomorphisms from `Γ(D(a) ∩ Spf A, 𝒪_{Spf A})` into a discrete
topological ring that agree on the restrictions of global sections are equal.

The two maps are a finite family of continuous homomorphisms into discrete rings, so by
`AlgebraicGeometry.exists_isIdealOfDefinition_forall_app_eq_zero` one ideal of definition `I`
serves both: each of them kills every section whose residue in `𝒪_I` vanishes. The sections of
`𝒪_I` over `D(a) ∩ Spf A` are the localization `(A/I)_{\bar a}`, so for a section `s` there are
`n` and `x : A` such that `a^n · s` and `x` have the same residue, where `a` and `x` stand for
the restrictions of the global sections they define. Both maps therefore send `a^n · s` to the
image of `x`, they agree on the images of `a` and of `x` by hypothesis, and the image of `a` is
invertible because `a` is invertible on `D(a) ∩ Spf A`. Cancelling that unit identifies the two
values at `s`.

The ideals-of-definition case of `spfPresheafOn_spfBasicOpen_hom_ext`. -/
theorem spfPresheaf_spfBasicOpen_hom_ext {T : TopCommRingCat.{u}} [DiscreteTopology T.α]
    (hA : IsPreAdmissible A) (a : A)
    {u v : (spfPresheaf A).obj (op (spfBasicOpen A a)) ⟶ T}
    (h : ∀ t : ((spfPresheaf A).obj (op ⊤)).α,
      u.1 (((spfPresheaf A).map (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op).1 t)
        = v.1 (((spfPresheaf A).map (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op).1 t)) :
    u = v :=
  spfPresheafOn_spfBasicOpen_hom_ext (A := A) (P := IsIdealOfDefinition) (T := T)
    (I₀ := preAdmissibleSpfIndex A hA) (a := a) (u := u) (v := v) (h := h)

end

/-! ### Maps into a pushforward of the structure presheaf -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- **Maps of the structure presheaf into a pushforward are determined by the global sections.**
Let `b : Spf B → Spf A` be a continuous map pulling every basic open of `Spf A` back to a
quasi-compact open. Two maps `𝒪_{Spf A} → b_* 𝒪_{Spf B}` of presheaves of topological rings that
agree on global sections are equal.

The basic opens form a basis of `Spf A` and `b_* 𝒪_{Spf B}` is a sheaf, so it is enough to
compare the two maps over a basic open; there the target is a limit of the terms `b_* 𝒪^B_J`, so
it is enough to compare after projecting onto one of them, and that projected target is discrete
because the preimage of the basic open is quasi-compact. The comparison is then
`AlgebraicGeometry.spfPresheafOn_spfBasicOpen_hom_ext`, whose hypothesis on the restrictions of
global sections is naturality together with the assumed agreement on global sections. -/
theorem spfPresheaf_pushforward_hom_ext (hA : IsPreAdmissible A) (hB : IsPreAdmissible B)
    (b : spfSpace B ⟶ spfSpace A)
    (hb : ∀ a : A, IsCompact ((((Opens.map b).obj (spfBasicOpen A a)) : Opens (spfSpace B)) :
      Set (spfSpace B)))
    {c c' : spfPresheaf A ⟶ b _* spfPresheaf B}
    (hΓ : c.app (op ⊤) = c'.app (op ⊤)) : c = c' := by
  refine TopCat.Sheaf.hom_ext (B := spfBasicOpen A) (spfPresheaf A)
    ⟨b _* spfPresheaf B, TopCat.Sheaf.pushforward_sheaf_of_sheaf b (isSheaf_spfPresheaf B hB)⟩
    (isBasis_spfBasicOpen A) fun a => ?_
  refine spfPresheafOn_obj_hom_ext B fun J => ?_
  have : DiscreteTopology ((pseudoDiscrete (spfComponentOn B J)).obj
      (op ((Opens.map b).obj (spfBasicOpen A a)))).α :=
    isPseudoDiscrete_pseudoDiscrete (spfComponentOn B J) _ (hb a)
  refine spfPresheafOn_spfBasicOpen_hom_ext A ⟨hA.choose, hA.choose_spec⟩ a fun t => ?_
  change ((spfProjectionOn B J).app (op ((Opens.map b).obj (spfBasicOpen A a)))).1
      ((c.app (op (spfBasicOpen A a))).1 _)
    = ((spfProjectionOn B J).app (op ((Opens.map b).obj (spfBasicOpen A a)))).1
      ((c'.app (op (spfBasicOpen A a))).1 _)
  rw [app_map_apply c, app_map_apply c', hΓ]

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- The map of spaces underlying `Spf φ` pulls the basic open `D(a) ∩ Spf A` back to
`D(φ a) ∩ Spf B`: an open prime `q` of `B` avoids `φ a` exactly when `φ⁻¹(q)` avoids `a`. -/
theorem spfMapBase_obj_spfBasicOpen {φ : A →+* B} (hφ : Continuous φ) (a : A) :
    (Opens.map (spfMapBase A B hφ)).obj (spfBasicOpen A a) = spfBasicOpen B (φ a) := rfl

/-- **A morphism out of `Spf B` into `Spf A` that agrees with `Spf φ` on the base and on global
sections is `Spf φ`.** The morphism of presheafed spaces is given by its base map `bm` and its
comparison map `cm` of sheaves; once the base maps agree, the comparison maps have the same type
and `AlgebraicGeometry.spfPresheaf_pushforward_hom_ext` identifies them, the hypothesis on
quasi-compact preimages holding because `Spf φ` pulls `D(a) ∩ Spf A` back to
`D(φ a) ∩ Spf B`. -/
theorem spfMap_eq_of_c_app_top_eq {φ : A →+* B} (hφ : Continuous φ) (hA : IsPreAdmissible A)
    (I₀ : IdealsOfDefinition A) (hB : IsPreAdmissible B)
    (bm : spfSpace B ⟶ spfSpace A) (cm : spfPresheaf A ⟶ bm _* spfPresheaf B)
    (hbase : spfMapBase A B hφ = bm)
    (hΓ : cm.app (op ⊤) = (spfMapC A B hφ I₀ hA).app (op ⊤)) :
    spfMap A B hφ I₀ hA = ⟨bm, cm⟩ := by
  subst hbase
  exact congrArg (fun k => (⟨spfMapBase A B hφ, k⟩ : Spf B ⟶ Spf A))
    (spfPresheaf_pushforward_hom_ext A B hA hB (spfMapBase A B hφ)
      (fun a => (spfMapBase_obj_spfBasicOpen A B hφ a) ▸
        isCompact_spfBasicOpen_of_isWeaklyPreAdmissible B
          (isWeaklyPreAdmissible_of_isPreAdmissible hB) (φ a))
      hΓ.symm)

end

/-! ### The bijection of Stacks 0AHZ -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] (hA : IsAdmissible A) (hB : IsAdmissible B) (I₀ : IdealsOfDefinition A)

/-- **Morphisms of formal spectra come from continuous ring maps.** Every morphism
`g : Spf B → Spf A` of locally topologically ringed spaces between the formal spectra of admissible
topological rings comes from a continuous ring homomorphism `A → B`, namely from
`AlgebraicGeometry.ltrsGlobalSectionsRingHom g`, the map `g` induces on global sections read
through the identifications `Γ(Spf A, 𝒪_{Spf A}) = A` and `Γ(Spf B, 𝒪_{Spf B}) = B` of Stacks 0AHY.
-/
@[stacks 0AHZ "surjectivity of the comparison map Hom_cont(A, B) → Mor_LTRS(Spf B, Spf A)",
  ega "I 10.2.2",
  ega "I 10.4.6" "Affine case X = Spf B", sga "3 VIIB 1.1" "partial"]
theorem surjective_spfLTRSMap : Function.Surjective (spfLTRSMap A B hA.1 I₀ hB.1) := by
  intro g
  refine ⟨ltrsGlobalSectionsTopHom A B hA hB g,
    LocallyTopologicallyRingedSpace.Hom.ext' (spfMap_eq_of_c_app_top_eq A B
      (continuous_ltrsGlobalSectionsRingHom A B hA hB g) hA.1 I₀ hB.1
      g.toHom.base g.toHom.c ?_ ?_)⟩
  · exact base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn A
      (ltrsGlobalSectionsMap_spfLTRSMap_ltrsGlobalSectionsTopHom A B hA hB I₀ g)
  · exact (spfMapGammaHom_ltrsGlobalSectionsRingHom A B hA hB I₀ g).symm

/-- **Stacks 0AHZ.** For admissible topological rings `A` and `B` the comparison map taking a
continuous ring homomorphism `A → B` to the induced morphism `Spf B → Spf A` of locally
topologically ringed spaces is a bijection: it is injective by
`AlgebraicGeometry.injective_spfLTRSMap`, separatedness of `B` making the canonical map
`B → Γ(Spf B, 𝒪_{Spf B})` injective, and surjective by
`AlgebraicGeometry.surjective_spfLTRSMap`. -/
@[stacks 0AHZ "the full bijection Hom_cont(A, B) = Mor_LTRS(Spf B, Spf A) for admissible A, B",
  sga "3 VIIB 1.1" "partial"]
theorem bijective_spfLTRSMap : Function.Bijective (spfLTRSMap A B hA.1 I₀ hB.1) :=
  let := hB.2.1
  ⟨injective_spfLTRSMap A B hA.1 I₀ hB.1, surjective_spfLTRSMap A B hA hB I₀⟩

/-- The identification `Hom_cont(A, B) = Mor_{LTRS}((Spf B, 𝒪_{Spf B}), (Spf A, 𝒪_{Spf A}))` for
admissible topological rings `A` and `B`, packaged from
`AlgebraicGeometry.bijective_spfLTRSMap` as an equivalence of types: a continuous ring
homomorphism `A → B` is exactly a morphism `A ⟶ B` of topological rings, and it corresponds to
the morphism of formal spectra it induces. -/
@[sga "3 VIIB 1.1" "partial"]
noncomputable def spfLTRSEquiv :
    (TopCommRingCat.of A ⟶ TopCommRingCat.of B) ≃ (spfLTRS B hB.1 ⟶ spfLTRS A hA.1) :=
  Equiv.ofBijective _ (bijective_spfLTRSMap A B hA hB I₀)

/-- The equivalence of Stacks 0AHZ sends a continuous ring homomorphism to the morphism of formal
spectra it induces. -/
@[simp]
theorem spfLTRSEquiv_apply (f : TopCommRingCat.of A ⟶ TopCommRingCat.of B) :
    spfLTRSEquiv A B hA hB I₀ f = spfLTRSMap A B hA.1 I₀ hB.1 f := rfl

end

end AlgebraicGeometry
