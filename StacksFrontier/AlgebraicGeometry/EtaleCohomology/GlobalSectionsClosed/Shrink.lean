module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Surjectivity

/-!
# Shrinking an étale neighbourhood so that a map into its base change is surjective

Let `i : Z ⟶ X` be a closed immersion and `F` a sheaf of sets on the small étale site of `X`.
A global section `t` of the inverse image `i^{-1}F` is, on a covering family `V j` of `Z`, the
pullback of sections `s j` of `F` over objects `W j` of the small étale site of `X`; this is
`Stacks.EtaleCohomology.exists_smallEtaleCover_lift_of_inverseImageSection`. The data carried by
that statement is awkward, because the `V j` persist in it and nothing says how much of
`W j ×_X Z` they see.

This file removes them. The image of `V j ⟶ W j ×_X Z` is open, because that morphism is étale;
and `W j ×_X Z ⟶ W j` is a closed immersion, because `i` is. So the image under that projection
of the complement of the image of `V j` is closed, and its complement is an open subscheme `Ω` of
`W j` — again an object of the small étale site of `X` — whose own base change is exactly the
image of `V j`. Replacing `W j` by `Ω`, the morphism `V j ⟶ Ω ×_X Z` is surjective, so on its own
it generates a covering sieve, and a sheaf is separated for its covering sieves: the identity
`t|_{V j} = i^{-1}(s j)|_{V j}` upgrades to `t|_{Ω ×_X Z} = i^{-1}(s j)`.

The result is
`Stacks.EtaleCohomology.exists_smallEtaleCover_sectionPullback_of_inverseImageSection`: a global
section of `i^{-1}F` is cut out by sections of `F` over a family of objects of the small étale
site of `X` *whose images cover `X`*, agreeing with it on the whole of each base change.
This is the state the source of [Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
reaches immediately before it invokes
[Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0).

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleRestrict` — an open subscheme of an object of the small étale
  site of `X`, as an object of that site.
* `Stacks.EtaleCohomology.smallEtaleRestrictHom` — the inclusion, as a morphism of the site.
* `Stacks.EtaleCohomology.smallEtaleSectionPullback` — the pullback `i^{-1}s` to `W ×_X Z` of a
  section `s` of `F` over `W`.

## Main results

* `Stacks.EtaleCohomology.map_smallEtaleRestrictHom_left_eq` and
  `Stacks.EtaleCohomology.range_map_smallEtaleRestrictHom_left` — base change along `i` of the
  inclusion of an open subscheme is an open immersion, with image the preimage of that open.
* `Stacks.EtaleCohomology.exists_smallEtaleRestrict_surjective` — the shrinking: an open
  subscheme of `W` through which a given `V ⟶ W ×_X Z` factors surjectively.
* `Stacks.EtaleCohomology.eq_of_map_eq_of_surjective` — a sheaf on the small étale site of `Z` is
  separated for a single morphism with surjective underlying map.
* `Stacks.EtaleCohomology.exists_smallEtaleCover_sectionPullback_of_inverseImageSection` — a
  global section of `i^{-1}F` comes from sections of `F` over a family covering `X`, agreeing
  with it over each whole base change.
* `Stacks.EtaleCohomology.surjective_smallEtaleGlobalSectionPullback_of_glue` — consequently the
  surjectivity half of Tag 09ZF needs only that such a family glue to a global section of `F`.

## Implementation notes

`Stacks.EtaleCohomology.smallEtaleRestrict` is built with `AlgebraicGeometry.Scheme.Etale.mk`,
which asks for the `Etale` instance on `Ω.ι ≫ W.hom`; the instance on `W.hom` is the object's own
property and has to be reintroduced by hand, exactly as in
`Stacks.EtaleCohomology.smallEtaleImage`.

The identification of `Ω ×_X Z` used here is `CategoryTheory.Limits.pullbackRightPullbackFstIso`,
which presents it as `Ω ×_W (W ×_X Z)`; in that presentation the map to `W ×_X Z` is a base
change of `Ω.ι`, which is what makes it an open immersion and gives its image. Several proofs in
this file are written as explicit chains of `Eq.trans` rather than with `rw`: the elaborated form
of `W.hom` for `W : X.Etale` passes `@Etale` where a `MorphismProperty Scheme` is expected, which
is well typed only at default transparency, and `rw` cannot abstract a pattern out of such a
term. The remedy of raising transparency by `set_option` is not used.

`Stacks.EtaleCohomology.isOpenImmersion_map_smallEtaleRestrictHom_left` is a global instance; its
head is the base change of one specific morphism, and `AlgebraicGeometry.IsOpenImmersion` is
`Prop`-valued, so it can create no instance diamond.

The covering family is indexed by `Type (u + 1)`, the object universe of the small étale site,
because it comes from `CategoryTheory.Sieve.exists_eq_ofArrows`; the singleton sieve used for
separatedness is therefore indexed by `PUnit.{u + 2}`.

What remains of Tag 09ZF is the step the source carries out with two external results, neither
of which is formalized here: a finite surjective `X' ⟶ X` Zariski-locally factoring through the
covering family ([Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0), More on
Morphisms 37.45.7, which is where quasi-compactness and quasi-separatedness of `X` enter), and
descent of sections of an étale sheaf of sets along a surjective integral morphism
([Stacks, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3), Remark 59.55.6). Hypothesis (2)
of the tag is consumed between them, along the finite morphism `X' ⟶ X`, and is therefore not a
hypothesis of anything in this file.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}

/-- An open subscheme of an object of the small étale site of `X`, as an object of that site:
an open immersion is étale and étale morphisms compose. -/
public def smallEtaleRestrict (W : X.Etale) (Ω : W.left.Opens) : X.Etale :=
  letI : Etale (W.hom : W.left ⟶ X) := W.prop
  Scheme.Etale.mk (Ω.ι ≫ (W.hom : W.left ⟶ X))

/-- The structure morphism of `smallEtaleRestrict W Ω` is the inclusion of `Ω` followed by the
structure morphism of `W`. -/
@[simp]
public theorem smallEtaleRestrict_hom (W : X.Etale) (Ω : W.left.Opens) :
    ((smallEtaleRestrict W Ω).hom : (smallEtaleRestrict W Ω).left ⟶ X)
      = Ω.ι ≫ (W.hom : W.left ⟶ X) := rfl

/-- The inclusion of an open subscheme of an object of the small étale site, as a morphism of
that site. -/
public def smallEtaleRestrictHom (W : X.Etale) (Ω : W.left.Opens) :
    smallEtaleRestrict W Ω ⟶ W :=
  MorphismProperty.Over.homMk Ω.ι rfl trivial

/-- The underlying morphism of schemes of `smallEtaleRestrictHom W Ω` is the inclusion of `Ω`. -/
@[simp]
public theorem smallEtaleRestrictHom_left (W : X.Etale) (Ω : W.left.Opens) :
    (smallEtaleRestrictHom W Ω).left = Ω.ι := rfl

variable {Z : Scheme.{u}} (i : Z ⟶ X)

/-- Base change along `i` of a morphism of the small étale site of `X`, composed with the first
projection of the fibre product. -/
public theorem map_smallEtaleBaseChange_left_fst {W W' : X.Etale} (r : W' ⟶ W) :
    ((smallEtaleBaseChange i).map r).left ≫ pullback.fst (W.hom : W.left ⟶ X) i
      = pullback.fst (W'.hom : W'.left ⟶ X) i ≫ r.left :=
  pullback.lift_fst _ _ _

/-- Base change along `i` of a morphism of the small étale site of `X`, composed with the second
projection of the fibre product: this is the structure morphism over `Z`. -/
public theorem map_smallEtaleBaseChange_left_snd {W W' : X.Etale} (r : W' ⟶ W) :
    ((smallEtaleBaseChange i).map r).left ≫ pullback.snd (W.hom : W.left ⟶ X) i
      = pullback.snd (W'.hom : W'.left ⟶ X) i :=
  MorphismProperty.Over.w ((smallEtaleBaseChange i).map r)

/-- Base change along `i` of the inclusion of an open subscheme is, under the canonical
identification `Ω ×_W (W ×_X Z) ≅ Ω ×_X Z`, the second projection of `Ω ×_W (W ×_X Z)`. -/
public theorem map_smallEtaleRestrictHom_left_eq (W : X.Etale) (Ω : W.left.Opens) :
    ((smallEtaleBaseChange i).map (smallEtaleRestrictHom W Ω)).left
      = (pullbackRightPullbackFstIso (W.hom : W.left ⟶ X) i Ω.ι).inv ≫
          pullback.snd Ω.ι (pullback.fst (W.hom : W.left ⟶ X) i) := by
  refine pullback.hom_ext
    ((map_smallEtaleBaseChange_left_fst i (smallEtaleRestrictHom W Ω)).trans ?_)
    ((map_smallEtaleBaseChange_left_snd i (smallEtaleRestrictHom W Ω)).trans ?_)
  · exact (congrArg (· ≫ Ω.ι)
        (pullbackRightPullbackFstIso_inv_fst (W.hom : W.left ⟶ X) i Ω.ι).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ (pullbackRightPullbackFstIso (W.hom : W.left ⟶ X) i Ω.ι).inv ≫ m)
          pullback.condition).trans (Category.assoc _ _ _).symm))
  · exact ((Category.assoc _ _ _).trans
      (pullbackRightPullbackFstIso_inv_snd_snd (W.hom : W.left ⟶ X) i Ω.ι)).symm

/-- Base change along `i` of the inclusion of an open subscheme is again an open immersion. -/
public instance isOpenImmersion_map_smallEtaleRestrictHom_left
    (W : X.Etale) (Ω : W.left.Opens) :
    IsOpenImmersion ((smallEtaleBaseChange i).map (smallEtaleRestrictHom W Ω)).left := by
  have h : IsOpenImmersion ((pullbackRightPullbackFstIso (W.hom : W.left ⟶ X) i Ω.ι).inv ≫
      pullback.snd Ω.ι (pullback.fst (W.hom : W.left ⟶ X) i)) := inferInstance
  rwa [map_smallEtaleRestrictHom_left_eq i W Ω]

/-- The image of `Ω ×_X Z` in `W ×_X Z` is the preimage of `Ω` under the first projection. -/
public theorem range_map_smallEtaleRestrictHom_left (W : X.Etale) (Ω : W.left.Opens) :
    Set.range ((smallEtaleBaseChange i).map (smallEtaleRestrictHom W Ω)).left.base
      = (pullback.fst (W.hom : W.left ⟶ X) i).base ⁻¹' (Ω : Set W.left) := by
  have hsurj : Function.Surjective
      (pullbackRightPullbackFstIso (W.hom : W.left ⟶ X) i Ω.ι).inv.base := Surjective.surj
  have happ : ∀ y, ((smallEtaleBaseChange i).map (smallEtaleRestrictHom W Ω)).left.base y
      = (pullback.snd Ω.ι (pullback.fst (W.hom : W.left ⟶ X) i)).base
        ((pullbackRightPullbackFstIso (W.hom : W.left ⟶ X) i Ω.ι).inv.base y) := by
    intro y
    rw [map_smallEtaleRestrictHom_left_eq]
    exact Scheme.Hom.comp_apply _ _ y
  refine Eq.trans (Set.Subset.antisymm ?_ ?_)
    ((Scheme.Pullback.range_snd Ω.ι (pullback.fst (W.hom : W.left ⟶ X) i)).trans
      (congrArg _ (Scheme.Opens.range_ι Ω)))
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, (happ y).symm⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨y', rfl⟩ := hsurj y
    exact ⟨y', happ y'⟩

/-- **Shrinking an étale neighbourhood to make a map into its base change surjective.** Let
`i : Z ⟶ X` be a closed immersion, `W` an object of the small étale site of `X`, and
`k : V ⟶ W ×_X Z` a morphism of the small étale site of `Z`. Then `W` has an open subscheme `Ω`
through which `k` factors, with `V ⟶ Ω ×_X Z` surjective.

The image of `k` is open in `W ×_X Z`, because `k` is étale; the projection `W ×_X Z ⟶ W` is a
closed immersion, because `i` is; so the image under that projection of the complement of the
image of `k` is closed, and `Ω` is its complement. Its preimage in `W ×_X Z` is exactly the
image of `k`, since the projection is injective. -/
public theorem exists_smallEtaleRestrict_surjective [IsClosedImmersion i]
    {W : X.Etale} {V : Z.Etale} (k : V ⟶ (smallEtaleBaseChange i).obj W) :
    ∃ (Ω : W.left.Opens) (k' : V ⟶ (smallEtaleBaseChange i).obj (smallEtaleRestrict W Ω)),
      k' ≫ (smallEtaleBaseChange i).map (smallEtaleRestrictHom W Ω) = k ∧
        Function.Surjective k'.left.base := by
  have hqinj : Function.Injective (pullback.fst (W.hom : W.left ⟶ X) i).base :=
    (IsClosedImmersion.isClosedEmbedding (pullback.fst (W.hom : W.left ⟶ X) i)).injective
  have hqcl : IsClosedMap (pullback.fst (W.hom : W.left ⟶ X) i).base :=
    Scheme.Hom.isClosedMap _
  have hkopen : IsOpen (Set.range k.left.base) := (Scheme.Hom.isOpenMap k.left).isOpen_range
  refine ⟨⟨((pullback.fst (W.hom : W.left ⟶ X) i).base '' (Set.range k.left.base)ᶜ)ᶜ,
    (hqcl _ hkopen.isClosed_compl).isOpen_compl⟩, ?_⟩
  set Ω : W.left.Opens :=
    ⟨((pullback.fst (W.hom : W.left ⟶ X) i).base '' (Set.range k.left.base)ᶜ)ᶜ,
      (hqcl _ hkopen.isClosed_compl).isOpen_compl⟩
  have hpre : ∀ p, (pullback.fst (W.hom : W.left ⟶ X) i).base p ∈ (Ω : Set W.left)
      ↔ p ∈ Set.range k.left.base := by
    intro p
    refine ⟨fun h ↦ ?_, fun hp h ↦ ?_⟩
    · by_contra hp
      exact h ⟨p, hp, rfl⟩
    · obtain ⟨p', hp', he⟩ := h
      obtain rfl := hqinj he
      exact hp' hp
  have hrange : Set.range (k.left ≫ pullback.fst (W.hom : W.left ⟶ X) i).base
      ⊆ Set.range (Ω.ι).base := by
    refine Set.range_subset_iff.2 fun v ↦ ?_
    have h1 : (pullback.fst (W.hom : W.left ⟶ X) i).base (k.left.base v) ∈ (Ω : Set W.left) :=
      (hpre _).2 ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (Scheme.Hom.comp_apply _ _ v).symm ▸ h1
  set a := IsOpenImmersion.lift Ω.ι (k.left ≫ pullback.fst (W.hom : W.left ⟶ X) i) hrange
  have hafac : a ≫ Ω.ι = k.left ≫ pullback.fst (W.hom : W.left ⟶ X) i :=
    IsOpenImmersion.lift_fac _ _ _
  have hw : a ≫ (Ω.ι ≫ (W.hom : W.left ⟶ X)) = (V.hom : V.left ⟶ Z) ≫ i :=
    (Category.assoc a Ω.ι (W.hom : W.left ⟶ X)).symm.trans
      ((congrArg (· ≫ (W.hom : W.left ⟶ X)) hafac).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun m ↦ k.left ≫ m) pullback.condition).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ i) (MorphismProperty.Over.w k))))))
  have hleft : pullback.lift a (V.hom : V.left ⟶ Z) hw ≫
      ((smallEtaleBaseChange i).map (smallEtaleRestrictHom W Ω)).left = k.left :=
    pullback.hom_ext
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ pullback.lift a (V.hom : V.left ⟶ Z) hw ≫ m)
            (map_smallEtaleBaseChange_left_fst i (smallEtaleRestrictHom W Ω))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ Ω.ι) (pullback.lift_fst a (V.hom : V.left ⟶ Z) hw)).trans hafac))))
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ pullback.lift a (V.hom : V.left ⟶ Z) hw ≫ m)
            (map_smallEtaleBaseChange_left_snd i (smallEtaleRestrictHom W Ω))).trans
          ((pullback.lift_snd a (V.hom : V.left ⟶ Z) hw).trans
            (MorphismProperty.Over.w k).symm)))
  refine ⟨MorphismProperty.Over.homMk (pullback.lift a (V.hom : V.left ⟶ Z) hw)
    (pullback.lift_snd _ _ _) trivial, MorphismProperty.Over.Hom.ext hleft, fun y ↦ ?_⟩
  have hmem : ((smallEtaleBaseChange i).map (smallEtaleRestrictHom W Ω)).left.base y
      ∈ Set.range k.left.base :=
    (hpre _).1 (Set.mem_preimage.1
      ((range_map_smallEtaleRestrictHom_left i W Ω).le (Set.mem_range_self y)))
  obtain ⟨v, hv⟩ := hmem
  refine ⟨v, (Scheme.Hom.isOpenEmbedding
    ((smallEtaleBaseChange i).map (smallEtaleRestrictHom W Ω)).left).injective ?_⟩
  exact ((Scheme.Hom.comp_apply _ _ v).symm.trans
    (congrArg (fun f ↦ f.base v) hleft)).trans hv

variable (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))

/-- The pullback `i⁻¹s` of a section `s` of `F` over an object `W` of the small étale site of
`X`, as a section of `i^{-1}F` over `W ×_X Z`: the unit of the left Kan extension along base
change, followed by the sheafification map. -/
public def smallEtaleSectionPullback (W : X.Etale) (s : F.obj.obj (op W)) :
    ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj
      (op ((smallEtaleBaseChange i).obj W)) :=
  (toSheafify (Scheme.smallEtaleTopology Z)
      ((smallEtaleBaseChange i).op.lan.obj F.obj)).app
      (op ((smallEtaleBaseChange i).obj W))
    (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W) s)

/-- Restricting `i⁻¹s` along a morphism into `W ×_X Z` is the sheafification map applied to the
corresponding restriction in the left Kan extension. -/
public theorem map_smallEtaleSectionPullback {W : X.Etale} {V : Z.Etale}
    (k : V ⟶ (smallEtaleBaseChange i).obj W) (s : F.obj.obj (op W)) :
    ((smallEtaleInverseImage.{u, v} i).obj F).obj.map k.op
        (smallEtaleSectionPullback.{u, v} i F W s)
      = (toSheafify (Scheme.smallEtaleTopology Z)
            ((smallEtaleBaseChange i).op.lan.obj F.obj)).app (op V)
          (((smallEtaleBaseChange i).op.lan.obj F.obj).map k.op
            (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W) s)) :=
  (NatTrans.naturality_apply (toSheafify (Scheme.smallEtaleTopology Z)
    ((smallEtaleBaseChange i).op.lan.obj F.obj)) k.op
      (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W) s)).symm

/-- Pullback of sections is compatible with restriction along a morphism of the small étale site
of `X`: this is naturality of the Kan extension unit and of the sheafification map. -/
public theorem smallEtaleSectionPullback_map {W W' : X.Etale} (r : W' ⟶ W)
    (s : F.obj.obj (op W)) :
    ((smallEtaleInverseImage.{u, v} i).obj F).obj.map ((smallEtaleBaseChange i).map r).op
        (smallEtaleSectionPullback.{u, v} i F W s)
      = smallEtaleSectionPullback.{u, v} i F W' (F.obj.map r.op s) :=
  (map_smallEtaleSectionPullback.{u, v} i F ((smallEtaleBaseChange i).map r) s).trans
    (congrArg ((toSheafify (Scheme.smallEtaleTopology Z)
        ((smallEtaleBaseChange i).op.lan.obj F.obj)).app (op ((smallEtaleBaseChange i).obj W')))
      (NatTrans.naturality_apply ((smallEtaleBaseChange i).op.lanUnit.app F.obj) r.op s).symm)

/-- Two sections of a sheaf on the small étale site of `Z` that agree after restriction along a
single morphism with surjective underlying map are equal: such a morphism generates a covering
sieve, and a sheaf is separated for its covering sieves. -/
public theorem eq_of_map_eq_of_surjective {U V : Z.Etale} (k : V ⟶ U)
    (hk : Function.Surjective k.left.base)
    (G : Sheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v)))
    {x y : G.obj.obj (op U)} (h : G.obj.map k.op x = G.obj.map k.op y) : x = y := by
  have hS : Sieve.ofArrows (fun _ : PUnit.{u + 2} ↦ V) (fun _ ↦ k)
      ∈ Scheme.smallEtaleTopology Z U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun w ↦ Set.mem_iUnion.2 ⟨PUnit.unit, hk w⟩
  refine (((isSheaf_iff_isSheaf_of_type _ _).1 G.property) _ hS).isSeparatedFor.ext ?_
  rintro Y f ⟨T, g, _, ⟨_⟩, rfl⟩
  rw [op_comp, G.obj.map_comp, types_comp_apply, types_comp_apply, h]

/-- **A global section of the inverse image is, on a covering of `X`, the pullback of a section
of `F`.** Let `i : Z ⟶ X` be a closed immersion such that restriction of global sections along
`i` is surjective for every sheaf of sets on the Zariski site of `X`. Then every global section
`t` of `i^{-1}F` is cut out by a family of objects `W j` of the small étale site of `X` whose
images cover `X`, together with sections `s j` of `F` over `W j` whose pullbacks `i⁻¹(s j)` are
the restrictions of `t` to the whole of `W j ×_X Z`.

This is the state the source of [Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
reaches before invoking [Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0): compared
with `Stacks.EtaleCohomology.exists_smallEtaleCover_covering_of_inverseImageSection` the
auxiliary covering of `Z` has disappeared from the statement, because each `W j` has been
shrunk — by `Stacks.EtaleCohomology.exists_smallEtaleRestrict_surjective` — until the member of
that covering surjects onto `W j ×_X Z`, and a sheaf is separated for the resulting covering. -/
public theorem exists_smallEtaleCover_sectionPullback_of_inverseImageSection
    [IsClosedImmersion i]
    (hZar : ∀ G : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Surjective (zariskiGlobalSectionsMap.{u, v} i G))
    (t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale))) :
    ∃ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
      (⨆ j, smallEtaleImage (W j)) = ⊤ ∧
        ∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
              (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
            = smallEtaleSectionPullback.{u, v} i F (W j) (s j) := by
  obtain ⟨α, V, p, W₀, k₀, s₀, hcov, ht⟩ :=
    exists_smallEtaleCover_lift_of_inverseImageSection.{u, v} i F t
  choose Ω k' hfac hsurj using fun j ↦ exists_smallEtaleRestrict_surjective i (k₀ j)
  refine ⟨α, fun j ↦ smallEtaleRestrict (W₀ j) (Ω j),
    fun j ↦ F.obj.map (smallEtaleRestrictHom (W₀ j) (Ω j)).op (s₀ j),
    iSup_smallEtaleImage_eq_top_of_zariski.{u, v} i hZar V p _ k' hcov, fun j ↦ ?_⟩
  refine eq_of_map_eq_of_surjective.{u, v} (k' j) (hsurj j) _ ?_
  have hterm : k' j ≫ terminal.from ((smallEtaleBaseChange i).obj
      (smallEtaleRestrict (W₀ j) (Ω j))) = p j := Subsingleton.elim _ _
  rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp, hterm, ← ht j,
    ← map_smallEtaleSectionPullback.{u, v} i F (k₀ j) (s₀ j), ← hfac j, op_comp,
    CategoryTheory.Functor.map_comp_apply,
    smallEtaleSectionPullback_map.{u, v} i F (smallEtaleRestrictHom (W₀ j) (Ω j))]

/-- **The surjectivity half of Tag 09ZF, reduced to gluing a family of local sections.** If every
family of sections of `F` over objects of the small étale site of `X` whose images cover `X`, and
whose pullbacks to `Z` are the restrictions of a given global section `t` of `i^{-1}F`, comes
from a global section of `F` with pullback `t`, then the presheaf-level pullback of global
sections is surjective — and so, by
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImageComparison_of_surjective`, the
comparison map of Tag 09ZF is an isomorphism.

Such a family exists for every `t` by
`Stacks.EtaleCohomology.exists_smallEtaleCover_sectionPullback_of_inverseImageSection`. -/
public theorem surjective_smallEtaleGlobalSectionPullback_of_glue [IsClosedImmersion i]
    (hZar : ∀ G : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Surjective (zariskiGlobalSectionsMap.{u, v} i G))
    (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale))
    (hglue : ∀ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
      (⨆ j, smallEtaleImage (W j)) = ⊤ →
      ∀ t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale)),
        (∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
              (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
            = smallEtaleSectionPullback.{u, v} i F (W j) (s j)) →
        ∃ a, smallEtaleGlobalSectionPullback.{u, v} i g F a = t) :
    Function.Surjective (smallEtaleGlobalSectionPullback.{u, v} i g F) := fun t ↦
  let ⟨α, W, s, hcov, ht⟩ :=
    exists_smallEtaleCover_sectionPullback_of_inverseImageSection.{u, v} i F hZar t
  hglue α W s hcov t ht

end Stacks.EtaleCohomology


namespace Stacks.EtaleCohomology
variable {X : Scheme.{u}}
variable {Z : Scheme.{u}} (i : Z ⟶ X)
variable (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

/-- **A global section of the inverse image is, on a covering of `X`, the pullback of a section
of `F`.** Let `i : Z ⟶ X` be a closed immersion such that the only open of `X` containing the
image of `i` is `X` itself. Then every global section `t` of `i^{-1}F` is cut out by a family of
objects `W j` of the small étale site of `X` whose images cover `X`, together with sections `s j`
of `F` over `W j` whose pullbacks `i⁻¹(s j)` are the restrictions of `t` to the whole of
`W j ×_X Z`. -/
public theorem exists_smallEtaleCover_sectionPullback_of_forall_eq_top
    [IsClosedImmersion i]
    (hstar : ∀ U : X.Opens, Set.range i.base ⊆ (U : Set X) → U = ⊤)
    (t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale))) :
    ∃ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
      (⨆ j, smallEtaleImage (W j)) = ⊤ ∧
        ∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
              (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
            = smallEtaleSectionPullback.{u, v} i F (W j) (s j) := by
  obtain ⟨α, V, p, W₀, k₀, s₀, hcov, ht⟩ :=
    exists_smallEtaleCover_lift_of_inverseImageSection.{u, v} i F t
  choose Ω k' hfac hsurj using fun j ↦ exists_smallEtaleRestrict_surjective i (k₀ j)
  refine ⟨α, fun j ↦ smallEtaleRestrict (W₀ j) (Ω j),
    fun j ↦ F.obj.map (smallEtaleRestrictHom (W₀ j) (Ω j)).op (s₀ j),
    iSup_smallEtaleImage_eq_top_of_forall_eq_top i hstar V p _ k' hcov, fun j ↦ ?_⟩
  refine eq_of_map_eq_of_surjective.{u, v} (k' j) (hsurj j) _ ?_
  have hterm : k' j ≫ terminal.from ((smallEtaleBaseChange i).obj
      (smallEtaleRestrict (W₀ j) (Ω j))) = p j := Subsingleton.elim _ _
  rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp, hterm, ← ht j,
    ← map_smallEtaleSectionPullback.{u, v} i F (k₀ j) (s₀ j), ← hfac j, op_comp,
    CategoryTheory.Functor.map_comp_apply,
    smallEtaleSectionPullback_map.{u, v} i F (smallEtaleRestrictHom (W₀ j) (Ω j))]

end Stacks.EtaleCohomology

end
