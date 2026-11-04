module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Intersections of closed subspaces, and the zero scheme of a section

An arbitrary intersection of closed subspaces of an algebraic space `F` over a scheme `S` is
again a closed subspace.  This is the one fact the scheme-theoretic intersection and union of
Tag 0CYZ and the zero scheme of Tag 0845 need in order to be honest data: each of the three is
defined as an infimum, in the complete lattice of subfunctors of `F`, of a *set of closed
subspaces*, and closedness of such an infimum does not depend on which set it is.

## Main definitions

* `AlgebraicGeometry.Space.ClosedSubspaces` is the ordered type of closed subspaces of `F`.
* `AlgebraicGeometry.Space.schemeTheoreticIntersection` and
  `AlgebraicGeometry.Space.schemeTheoreticUnion` are the two operations of Tag 0CYZ: the
  intersection of two closed subspaces, and their smallest common closed superspace, the latter
  built from `AlgebraicGeometry.Space.unionSubfunctor`.
* `AlgebraicGeometry.Space.definingIdealAt` is the ideal of a closed subspace on an object of
  the small étale site: the kernel of the structure map of its inclusion.
* `AlgebraicGeometry.Space.zeroSchemeSubfunctor` is the subfunctor of Tag 0845 cut out by
  evaluation at a section of an `𝒪_F`-module, and `AlgebraicGeometry.Space.zeroScheme` bundles
  it with its closedness.

## Main results

* `AlgebraicGeometry.Space.isClosedSubspace_sInf`: an intersection of closed subspaces of an
  algebraic space is a closed subspace.  Its two halves are
  `AlgebraicGeometry.Space.isSheaf_sInf_toFunctor` and
  `AlgebraicGeometry.Space.isClosedImmersion_ι_sInf`.
* `AlgebraicGeometry.Space.inf_isClosedSubspace` and
  `AlgebraicGeometry.Space.unionSubfunctor_isClosedSubspace` are the two closedness assertions
  of Tag 0CYZ, and `AlgebraicGeometry.Space.zeroSchemeSubfunctor_isClosedSubspace` the one of
  Tag 0845.

## Implementation notes

Closedness of `sInf 𝒮` is proved directly, with no reference to quasi-coherent ideal sheaves,
and in particular without the correspondence of Tag 03MB between closed subspaces and
quasi-coherent ideals, which is not available.  Both halves of
`AlgebraicGeometry.IsAlgebraicSpace` are then in reach:

* the inclusion of `sInf 𝒮` is a closed immersion because its base change along a morphism from
  an object `a` of the site is *represented* by the scheme-theoretic intersection, inside `a`, of
  the represented base changes of the members of `𝒮` — the closed subscheme cut out by the sum of
  their ideal sheaves, which Tag 000R(4) keeps inside the site.  The universal property of that
  intersection says exactly that a morphism of the site into `a` factors through it as soon as it
  factors through every member, and under
  `AlgebraicGeometry.Space.mem_obj_iff_exists_comp` — which reads membership in a subfunctor off a
  represented base change of its inclusion — that is the statement that a section of `F` lies in
  every member of `𝒮`, i.e. in `sInf 𝒮`.  The resulting square is cartesian because `Subfunctor.ι`
  is a monomorphism, so no comparison beyond that factorization is needed;
* `sInf 𝒮` is then an algebraic space by
  `AlgebraicGeometry.IsAlgebraicSpace.of_relativelyRepresentable`
  (Tag 02WY) once it is a sheaf, which it is because an intersection of sheaf subfunctors of a
  sheaf is a sheaf: the covering sieve of a section of the intersection is contained in the
  covering sieve for each member.  Note that the *supremum* of subfunctors is `obj`-wise union and
  is in general not a sheaf — see `AlgebraicGeometry.Space.schematicLocus` — so the argument is
  specific to infima.

No hypothesis of invertibility, local freeness or quasi-coherence is used anywhere, so
`zeroSchemeSubfunctor_isClosedSubspace` is stated for a section of an arbitrary `𝒪_F`-module,
dropping the `IsInvertible` instance of the source.

`definingIdealAt` is the kernel of `AlgebraicGeometry.Space.structureSharp`, the structure map
`f♯ : 𝒪_F ⟶ f_*𝒪_Z` of Tag 03G8.  Tag 03G8 also asserts a morphism of small étale *ringed topoi*,
of which `f♯` is one component; that morphism is not available (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp`), and it is not needed here, since only
the structure map enters the kernel.

The identifications of these defining ideals — the sum and the intersection of the two ideals for
Tag 0CYZ, and the image of evaluation for Tag 0845 — are *not* proved here.  They are the content
of Tag 03MB in the direction which produces a closed subspace from a prescribed quasi-coherent
ideal, and the library has no quasi-coherent ideals on an algebraic space at all.

## References

* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

section Intersections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Membership in a subfunctor and represented base changes -/

/-- A section of the ambient presheaf, taken over a represented base change of the inclusion
of a subfunctor, lies in the subfunctor exactly when it factors through the representing
object of that base change. -/
theorem mem_obj_iff_exists_comp (Z : Subfunctor F) {a b : BigFppfOver B S hS}
    {g : yoneda.obj a ⟶ F} {fst : yoneda.obj b ⟶ Z.toFunctor} {snd : b ⟶ a}
    (sq : IsPullback fst (yoneda.map snd) Z.ι g)
    (U : (BigFppfOver B S hS)ᵒᵖ) (h : U.unop ⟶ a) :
    g.app U h ∈ Z.obj U ↔ ∃ ψ : U.unop ⟶ b, ψ ≫ snd = h := by
  have hy : yonedaEquiv (yoneda.map h ≫ g) = g.app U h := by
    simp [yonedaEquiv]
  rw [← hy, Subfunctor.mem_obj_iff_exists]
  constructor
  · rintro ⟨χ, hχ⟩
    refine ⟨yoneda.preimage (sq.lift χ (yoneda.map h) hχ), ?_⟩
    apply Functor.map_injective (yoneda (C := BigFppfOver B S hS))
    rw [Functor.map_comp, Functor.map_preimage]
    exact sq.lift_snd _ _ _
  · rintro ⟨ψ, rfl⟩
    exact ⟨yoneda.map ψ ≫ fst, by
      rw [Category.assoc, sq.w, ← Category.assoc, ← Functor.map_comp]⟩

/-! ### Intersections of closed subspaces -/

/-- Sections of an intersection of subfunctors are the sections lying in every member. -/
private lemma mem_sInf_obj (𝒮 : Set (Subfunctor F)) (U : (BigFppfOver B S hS)ᵒᵖ)
    (x : F.obj U) : x ∈ (sInf 𝒮).obj U ↔ ∀ Z ∈ 𝒮, x ∈ Z.obj U := by
  rw [Subfunctor.sInf_obj, Set.sInf_eq_sInter, Set.mem_sInter]
  refine ⟨fun hx Z hZ => hx _ ⟨Z, hZ, rfl⟩, ?_⟩
  rintro hx _ ⟨Z, hZ, rfl⟩
  exact hx Z hZ

/-- An intersection of subfunctors of a sheaf, each of which is a sheaf, is a sheaf. -/
theorem isSheaf_sInf_toFunctor (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (𝒮 : Set (Subfunctor F))
    (h : ∀ Z ∈ 𝒮, Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z.toFunctor) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (sInf 𝒮).toFunctor := by
  have hF' := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ hF']
  intro U s hs
  refine (mem_sInf_obj B S hS 𝒮 U s).2 fun Z hZ => ?_
  refine (Subfunctor.isSheaf_iff Z hF').1 ((isSheaf_iff_isSheaf_of_type _ _).1 (h Z hZ)) U s ?_
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hs
  intro V i hi
  exact (mem_sInf_obj B S hS 𝒮 (op V) _).1 hi Z hZ

/-- The inclusion of an intersection of closed subspaces is a closed immersion.

The represented base change of the intersection along a morphism from an object `a` of the
site is the scheme-theoretic intersection, inside `a`, of the represented base changes of the
members of the family: the closed subscheme cut out by the sum of their ideal sheaves, whose
size Stacks 000R(4) bounds, so that it is again an object of the site. -/
theorem isClosedImmersion_ι_sInf (𝒮 : Set (Subfunctor F))
    (h : ∀ Z ∈ 𝒮, IsClosedImmersion B S hS Z.ι) :
    IsClosedImmersion B S hS (sInf 𝒮).ι := by
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro a g
  choose Zb sn fs hpb using fun i : ↥𝒮 => (h i.1 i.2).rep g
  have hci : ∀ i, _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (sn i)) := fun i =>
    (h i.1 i.2).property g (fs i) (sn i) (hpb i)
  obtain ⟨b, snb, hsnb, hpex, hlift⟩ := exists_siteClosedInter B S hS a Zb sn hci
  have := hsnb
  have hmono : Mono snb :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map (f := snb) inferInstance
  -- A section of `F` over `a` lies in the intersection exactly when the corresponding
  -- morphism of the site factors through the scheme-theoretic intersection.
  have hmemb : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (t : U.unop ⟶ a),
      g.app U t ∈ (sInf 𝒮).obj U ↔ ∃ ψ : U.unop ⟶ b, ψ ≫ snb = t := by
    intro U t
    constructor
    · intro hmem
      exact hlift U.unop t fun i =>
        (mem_obj_iff_exists_comp B S hS i.1 (hpb i) U t).1
          ((mem_sInf_obj B S hS 𝒮 U _).1 hmem i.1 i.2)
    · rintro ⟨ψ, rfl⟩
      refine (mem_sInf_obj B S hS 𝒮 U _).2 fun Z hZ => ?_
      obtain ⟨q, hq⟩ := hpex ⟨Z, hZ⟩
      exact (mem_obj_iff_exists_comp B S hS Z (hpb ⟨Z, hZ⟩) U _).2
        ⟨ψ ≫ q, by rw [Category.assoc, hq]⟩
  have hrange : Subfunctor.range (yoneda.map snb ≫ g) ≤ sInf 𝒮 := by
    rintro U _ ⟨k, rfl⟩
    exact (hmemb U (k ≫ snb)).2 ⟨k, rfl⟩
  set p := Subfunctor.lift (yoneda.map snb ≫ g) hrange with hp
  have hw : p ≫ (sInf 𝒮).ι = yoneda.map snb ≫ g := Subfunctor.lift_ι _ _
  have key : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (u : T ⟶ (sInf 𝒮).toFunctor)
      (t : T ⟶ yoneda.obj a), u ≫ (sInf 𝒮).ι = t ≫ g →
      ∃ m : T ⟶ yoneda.obj b, m ≫ yoneda.map snb = t := by
    intro T u t hut
    have hfac : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (x : T.obj U),
        ∃ ψ : U.unop ⟶ b, ψ ≫ snb = t.app U x := by
      intro U x
      refine (hmemb U (t.app U x)).1 ?_
      have hx : ((u.app U x : (sInf 𝒮).toFunctor.obj U) : F.obj U) = g.app U (t.app U x) :=
        congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
          (congrArg (fun k => NatTrans.app k U) hut)) x
      exact hx ▸ (u.app U x).2
    choose mm hmm using hfac
    refine ⟨{ app := fun U => ↾(mm U), naturality := ?_ }, ?_⟩
    · intro U U' k
      ext x
      show mm U' (T.map k x) = k.unop ≫ mm U x
      rw [← cancel_mono snb, Category.assoc, hmm, hmm]
      exact ConcreteCategory.congr_hom (t.naturality k) x
    · ext U x
      exact hmm U x
  refine ⟨b, p, snb, IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => (key s.pt s.fst s.snd s.condition).choose) (fun s => ?_)
    (fun s => (key s.pt s.fst s.snd s.condition).choose_spec) (fun s m _ h₂ => ?_)), hsnb⟩
  · rw [← cancel_mono (sInf 𝒮).ι, Category.assoc, hw, ← Category.assoc,
      (key s.pt s.fst s.snd s.condition).choose_spec, s.condition]
  · rw [← cancel_mono (yoneda.map snb), h₂,
      (key s.pt s.fst s.snd s.condition).choose_spec]

/-- **The intersection of a family of closed subspaces is a closed subspace.** -/
theorem isClosedSubspace_sInf (hF : IsAlgebraicSpace B S hS F) (𝒮 : Set (Subfunctor F))
    (h : ∀ Z ∈ 𝒮, IsClosedSubspace B S hS Z) :
    IsClosedSubspace B S hS (sInf 𝒮) :=
  have hci : IsClosedImmersion B S hS (sInf 𝒮).ι :=
    isClosedImmersion_ι_sInf B S hS 𝒮 fun Z hZ => (h Z hZ).2
  ⟨IsAlgebraicSpace.of_relativelyRepresentable
    (isSheaf_sInf_toFunctor B S hS hF.isSheaf 𝒮 fun Z hZ => (h Z hZ).1.isSheaf) hF hci.rep,
    hci⟩

end Intersections

/-! ### Closed subspaces and their defining ideals -/

section ClosedSubspaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 0CYZ.** Closed subspaces of an algebraic space, regarded as subfunctors. -/
abbrev ClosedSubspaces :=
  {Z : Subfunctor F // IsClosedSubspace B S hS Z}

/-- The intersection of two closed subspaces is again a closed subspace. -/
theorem inf_isClosedSubspace (hF : IsAlgebraicSpace B S hS F)
    (Z Y : ClosedSubspaces B S hS F) :
    IsClosedSubspace B S hS (Z.1 ⊓ Y.1) := by
  rw [← sInf_pair]
  refine isClosedSubspace_sInf B S hS hF _ ?_
  rintro W (rfl | rfl)
  exacts [Z.2, Y.2]

/-- **Stacks 0CYZ.** The closed subspace cut out by the sum of the defining quasi-coherent
ideal sheaves. -/
@[stacks 0CYZ "scheme-theoretic intersection"]
def schemeTheoreticIntersection (hF : IsAlgebraicSpace B S hS F)
    (Z Y : ClosedSubspaces B S hS F) :
    ClosedSubspaces B S hS F :=
  ⟨Z.1 ⊓ Y.1, inf_isClosedSubspace B S hS F hF Z Y⟩

/-- The subfunctor underlying the smallest closed superspace of `Z` and `Y`. -/
def unionSubfunctor (Z Y : ClosedSubspaces B S hS F) : Subfunctor F :=
  sInf {W : Subfunctor F |
    IsClosedSubspace B S hS W ∧ Z.1 ≤ W ∧ Y.1 ≤ W}

/-- The smallest common closed superspace is again a closed subspace. -/
theorem unionSubfunctor_isClosedSubspace (hF : IsAlgebraicSpace B S hS F)
    (Z Y : ClosedSubspaces B S hS F) :
    IsClosedSubspace B S hS (unionSubfunctor B S hS F Z Y) :=
  isClosedSubspace_sInf B S hS hF _ fun _ hW => hW.1

/-- **Stacks 0CYZ.** The closed subspace cut out by the intersection of the defining
quasi-coherent ideal sheaves. -/
@[stacks 0CYZ "scheme-theoretic union"]
def schemeTheoreticUnion (hF : IsAlgebraicSpace B S hS F)
    (Z Y : ClosedSubspaces B S hS F) :
    ClosedSubspaces B S hS F :=
  ⟨unionSubfunctor B S hS F Z Y,
    unionSubfunctor_isClosedSubspace B S hS F hF Z Y⟩

end ClosedSubspaces

section DefiningIdeal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The defining ideal of a closed subspace on an object of the small étale site: the kernel
of the structure map of its inclusion. -/
noncomputable def definingIdealAt (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ) :=
  let W : AlgebraicSpaces B S hS := ⟨Z.1.toFunctor, Z.2.1⟩
  let i : W ⟶ X := ObjectProperty.homMk Z.1.ι
  RingHom.ker ((structureSharp B S hS i).hom.app U).hom

/-! ### The zero scheme of a section -/

/-- **Stacks 0845.** Intersect the closed subspaces whose defining ideals are contained in the
ideals generated by local evaluations of the section. -/
@[stacks 0845 "underlying subfunctor construction"]
noncomputable def zeroSchemeSubfunctor (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections) : Subfunctor X.1 :=
  sInf {Z | ∃ hZ : IsClosedSubspace B S hS Z,
    ∀ U : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toSchemes B S hS X.1).obj U).1 →
      definingIdealAt B S hS X ⟨Z, hZ⟩ (op U) ≤
        Ideal.span (Set.range (fun l : Module.Dual
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op U))
          (L.val.obj (op U)) => l (s.eval (op U))))}

/-- **Stacks 0845.** The subfunctor cut out by evaluation at a section of a module sheaf is a
closed subspace. -/
@[stacks 0845 "closedness"]
theorem zeroSchemeSubfunctor_isClosedSubspace (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections) :
    IsClosedSubspace B S hS (zeroSchemeSubfunctor B S hS X L s) :=
  isClosedSubspace_sInf B S hS X.2 _ fun _ hZ => hZ.elim fun h _ => h

/-- The zero scheme of a section, as a bundled closed subspace. -/
noncomputable abbrev zeroScheme (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections) :
    ClosedSubspaces B S hS X.1 :=
  ⟨zeroSchemeSubfunctor B S hS X L s,
    zeroSchemeSubfunctor_isClosedSubspace B S hS X L s⟩

end DefiningIdeal

end Space

end AlgebraicGeometry

end
