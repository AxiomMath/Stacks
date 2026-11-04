module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Coherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.ConstantMorphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Empty
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.MemberSystem

/-!
# Morphisms of constant sheaves along a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact, quasi-separated
schemes with affine transition morphisms inside a big étale site, and let `E`, `E'` be values in a
coefficient category, `E` finite (sets, abelian groups) or finitely generated (modules). This
file proves the case of constant sheaves of Stacks Tag 0GL2: morphisms from the constant sheaf
on `E` to the constant sheaf on `E'` on `X_étale` are the colimit of those on the
`(X_i)_étale`.

Morphisms between constant sheaves on different schemes are compared through *transport*
`AlgebraicGeometry.smallEtaleConstantTransport`: the inverse image along `f : T ⟶ S`, read between
constant sheaves through `AlgebraicGeometry.smallEtaleConstantPullbackIso`. Transport is
functorial in `f` and fixes constant sheaf maps.

## Strategy

Both halves of the statement are proved by the same mechanism. A morphism of constant sheaves is
locally constant (`AlgebraicGeometry.exists_cover_smallEtaleSheafPullback_map_eq`), so it is the
constant map `g_k` over the members of a covering, which can be taken finite with affine members
(Tag 0EYL). Over a quasi-compact, quasi-separated étale `W` at a stage, two constant values which
agree over the base change `W ×_{X_i} X` agree outright, unless that base change is empty
(the constant sheaf functor is faithful on a nonempty scheme), and in the latter case the base
changes `W ×_{X_i} X_j` are empty for all late `j` (Tag 05F3, applied to the member system of
`W`), where any two morphisms agree.

* *Injectivity.* Two morphisms at a stage with equal transports to `X` are constant on a common
  finite affine covering; on each member the values agree or the member becomes empty, so at a
  late stage the transports agree on the base change of the covering, hence agree.
* *Surjectivity.* A morphism at `X` is constant on the base change of a finite affine covering
  at a stage; on overlaps of two members the values agree or the overlap becomes empty, so at a
  late stage the constant maps glue to a morphism there, whose transport to `X` agrees with the
  given one on the covering.

## Main definitions

* `AlgebraicGeometry.smallEtaleConstantTransport` — the transport of a morphism of constant
  sheaves along a morphism of schemes.
* `AlgebraicGeometry.SmallEtaleConstantMapsLocallyConstant`,
  `AlgebraicGeometry.SmallEtaleConstantFaithful` — the two properties of the coefficient
  category the argument uses.

## Main results

* `AlgebraicGeometry.exists_smallEtaleConstantTransport_eq_of_compatible` — morphisms of constant
  sheaves glue along a covering, in transported form.
* `AlgebraicGeometry.exists_stage_transport_eq_of_transport_eq` — injectivity, for a general
  coefficient category, and its three specializations.
* `AlgebraicGeometry.exists_stage_transport_eq` — surjectivity, for a general coefficient
  category, and its three specializations.
* `AlgebraicGeometry.exists_stage_transport_iso` — isomorphisms of constant sheaves at `X` come
  from a stage, for a general coefficient category, and its three specializations.

## References

* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 05F3](https://stacks.math.columbia.edu/tag/05F3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

section Transport

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **Transport of a morphism of constant sheaves along a morphism of schemes.** For `f : T ⟶ S`
and a morphism `a` from the constant sheaf on `E` to the constant sheaf on `E'` on the small étale
site of `S`, the inverse image of `a` along `f`, read between the constant sheaves on `E` and `E'`
on the small étale site of `T` through `AlgebraicGeometry.smallEtaleConstantPullbackIso`. -/
public def smallEtaleConstantTransport {S T : B.Scheme} (f : T ⟶ S) {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E') :
    (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E' :=
  (smallEtaleConstantPullbackIso B A f E).inv ≫ (smallEtaleSheafPullback B A f).map a ≫
    (smallEtaleConstantPullbackIso B A f E').hom

/-- The inverse image of a morphism of constant sheaves is determined by its transport. -/
public theorem smallEtaleSheafPullback_map_eq_iff {S T : B.Scheme} (f : T ⟶ S) {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E')
    (b : (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E') :
    (smallEtaleSheafPullback B A f).map a =
        (smallEtaleConstantPullbackIso B A f E).hom ≫ b ≫
          (smallEtaleConstantPullbackIso B A f E').inv ↔
      smallEtaleConstantTransport B A f a = b := by
  rw [smallEtaleConstantTransport, Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]

/-- Transport commutes with composition of morphisms of sheaves. -/
@[simp]
public theorem smallEtaleConstantTransport_comp {S T : B.Scheme} (f : T ⟶ S) {E E' E'' : A}
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E')
    (b : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E' ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E'') :
    smallEtaleConstantTransport B A f (a ≫ b) =
      smallEtaleConstantTransport B A f a ≫ smallEtaleConstantTransport B A f b := by
  simp [smallEtaleConstantTransport]

/-- Transport preserves identities. -/
@[simp]
public theorem smallEtaleConstantTransport_id {S T : B.Scheme} (f : T ⟶ S) (E : A) :
    smallEtaleConstantTransport B A f
        (𝟙 ((constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E)) = 𝟙 _ := by
  simp [smallEtaleConstantTransport]

/-- Transport of a constant sheaf map is the same constant sheaf map. -/
@[simp]
public theorem smallEtaleConstantTransport_constantSheaf_map {S T : B.Scheme} (f : T ⟶ S)
    {E E' : A} (g : E ⟶ E') :
    smallEtaleConstantTransport B A f
        ((constantSheaf (SmallEtale.topology B S.obj S.property) A).map g) =
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).map g := by
  rw [smallEtaleConstantTransport, smallEtaleConstantPullbackIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- The comparison of the inverse image along a named composite `f ≫ g = h` with the constant
sheaf, in terms of the comparisons along `f` and `g`. -/
private theorem smallEtaleConstantPullbackIso_comp' {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (F : A) :
    smallEtaleConstantPullbackIso B A h F =
      ((smallEtaleSheafPullbackCompIso' B A f g h e).app
          ((constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj F)).symm ≪≫
        (smallEtaleSheafPullback B A f).mapIso (smallEtaleConstantPullbackIso B A g F) ≪≫
          smallEtaleConstantPullbackIso B A f F :=
  Iso.ext (smallEtaleSheafPullbackCompIso'_inv_app_constantSheaf B A f g h e F).symm

/-- **Transport along a composite is the composite of the transports**, for a named composite
`f ≫ g = h`. -/
public theorem smallEtaleConstantTransport_comp' {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E') :
    smallEtaleConstantTransport B A h a =
      smallEtaleConstantTransport B A f (smallEtaleConstantTransport B A g a) := by
  have hn := (smallEtaleSheafPullbackCompIso' B A f g h e).hom.naturality a
  simp only [Functor.comp_map] at hn
  simp only [smallEtaleConstantTransport, smallEtaleConstantPullbackIso_comp' B A f g h e,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]

/-- Transport of a morphism of constant sheaves only depends on its inverse image. -/
public theorem smallEtaleSheafPullback_map_eq_of_transport_eq {S T : B.Scheme} (f : T ⟶ S)
    {E E' : A}
    {a b : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E'}
    (h : smallEtaleConstantTransport B A f a = smallEtaleConstantTransport B A f b) :
    (smallEtaleSheafPullback B A f).map a = (smallEtaleSheafPullback B A f).map b := by
  rw [(smallEtaleSheafPullback_map_eq_iff B A f a _).mpr rfl, h,
    smallEtaleConstantTransport, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

/-- **The constancy sieve.** The sieve of objects `W` of the small étale site of `S` over which a
morphism `a` of constant sheaves is constant: its transport along the structure morphism of `W`
is a constant sheaf map. -/
public def smallEtaleConstancySieve {S : B.Scheme} {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E') :
    Sieve (SmallEtale.final B S.obj S.property) where
  arrows W _ := ∃ g : E ⟶ E', smallEtaleConstantTransport B A W.obj.hom a =
    (constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).map g
  downward_closed {W W'} _ := by
    rintro ⟨g, hg⟩ q
    refine ⟨g, ?_⟩
    rw [smallEtaleConstantTransport_comp' B A q.hom.left W.obj.hom W'.obj.hom (Over.w q.hom),
      hg, smallEtaleConstantTransport_constantSheaf_map]

/-- Membership in the constancy sieve. -/
public theorem smallEtaleConstancySieve_apply {S : B.Scheme} {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E')
    {W : SmallEtale B S.obj S.property} (q : W ⟶ SmallEtale.final B S.obj S.property) :
    smallEtaleConstancySieve B A a q ↔ ∃ g : E ⟶ E', smallEtaleConstantTransport B A W.obj.hom a =
      (constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).map g :=
  Iff.rfl

/-- A morphism of constant sheaves which is locally constant on a covering has a covering
constancy sieve. -/
public theorem smallEtaleConstancySieve_mem {S : B.Scheme} {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E')
    {K : Type*} (V : K → SmallEtale B S.obj S.property)
    (hV : Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    (g : K → (E ⟶ E'))
    (hg : ∀ k, (smallEtaleSheafPullback B A (V k).obj.hom).map a =
      (smallEtaleConstantPullbackIso B A (V k).obj.hom E).hom ≫
        (constantSheaf (SmallEtale.topology B (V k).obj.left.obj (V k).obj.left.property) A).map
          (g k) ≫ (smallEtaleConstantPullbackIso B A (V k).obj.hom E').inv) :
    smallEtaleConstancySieve B A a ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) := by
  refine (SmallEtale.topology B S.obj S.property).superset_covering ?_ hV
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨k⟩
  exact ⟨g k, (smallEtaleSheafPullback_map_eq_iff B A _ a _).mp (hg k)⟩

/-- Constancy is inherited along composites: if the transport of `a` along `g` is the constant
sheaf map attached to `x`, so is its transport along any `h = f ≫ g`. -/
public theorem smallEtaleConstantTransport_eq_of_comp {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) {E E' : A}
    {a : (constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E'} {x : E ⟶ E'}
    (ha : smallEtaleConstantTransport B A g a =
      (constantSheaf (SmallEtale.topology B Y.obj Y.property) A).map x) :
    smallEtaleConstantTransport B A h a =
      (constantSheaf (SmallEtale.topology B X.obj X.property) A).map x := by
  rw [smallEtaleConstantTransport_comp' B A f g h e, ha,
    smallEtaleConstantTransport_constantSheaf_map]

/-- **Constancy over a member is inherited by its base change.** If the transport of `a` along
the structure morphism of `W` is the constant sheaf map attached to `x`, then for `f : T ⟶ S` the
transport of the transport of `a` along `f`, along the structure morphism of the base change of
`W` to `T`, is the constant sheaf map attached to `x` as well. -/
public theorem smallEtaleConstantTransport_baseChange {S T : B.Scheme} (f : T ⟶ S)
    (W : SmallEtale B S.obj S.property) {E E' : A}
    {a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E'} {x : E ⟶ E'}
    (ha : smallEtaleConstantTransport B A W.obj.hom a =
      (constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).map x) :
    smallEtaleConstantTransport B A ((smallEtaleBaseChange B f).obj W).obj.hom
        (smallEtaleConstantTransport B A f a) =
      (constantSheaf (SmallEtale.topology B ((smallEtaleBaseChange B f).obj W).obj.left.obj
        ((smallEtaleBaseChange B f).obj W).obj.left.property) A).map x := by
  refine (smallEtaleConstantTransport_comp' B A ((smallEtaleBaseChange B f).obj W).obj.hom f
    (pullback.fst W.obj.hom f ≫ W.obj.hom) pullback.condition.symm a).symm.trans ?_
  exact smallEtaleConstantTransport_eq_of_comp B A (pullback.fst W.obj.hom f) W.obj.hom _ rfl ha

/-- **The comparison along a named composite, on morphisms of constant sheaves.** For
`f ≫ g = h`, conjugating the inverse image along `f` of (the inverse image along `g` of) a
morphism `c` of constant sheaves by the comparison
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` gives the transport of `c` along `f`, read
through the comparison of the inverse image along `h` with the constant sheaf. -/
public theorem smallEtaleSheafPullbackCompIso'_conj_constantSheaf {X Y Z : B.Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h) {E E' : A}
    (c : (constantSheaf (SmallEtale.topology B Y.obj Y.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B Y.obj Y.property) A).obj E') :
    (smallEtaleSheafPullbackCompIso' B A f g h e).inv.app
        ((constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E) ≫
      (smallEtaleSheafPullback B A f).map ((smallEtaleConstantPullbackIso B A g E).hom ≫ c ≫
        (smallEtaleConstantPullbackIso B A g E').inv) ≫
      (smallEtaleSheafPullbackCompIso' B A f g h e).hom.app
        ((constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E') =
    (smallEtaleConstantPullbackIso B A h E).hom ≫ smallEtaleConstantTransport B A f c ≫
      (smallEtaleConstantPullbackIso B A h E').inv := by
  rw [smallEtaleConstantPullbackIso_comp' B A f g h e E,
    smallEtaleConstantPullbackIso_comp' B A f g h e E']
  simp [smallEtaleConstantTransport]

end Transport

section Refine

variable (B : BigEtaleSite.{u})

/-- **A covering sieve of a quasi-compact, quasi-separated scheme contains a finite affine
covering.** Every covering sieve of the final object of the small étale site of a quasi-compact,
quasi-separated `S` contains the arrows of a finite family of objects with affine underlying
schemes which covers the final object.

This is `AlgebraicGeometry.smallEtaleStagesCoveringsRefine_affine_of_isLimit` for the constant
inverse system with value `S`, indexed by a point. -/
public theorem exists_finite_affine_le_sieve (S : B.Scheme) [CompactSpace S.obj]
    [QuasiSeparatedSpace S.obj] (R : Sieve (SmallEtale.final B S.obj S.property))
    (hR : R ∈ SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property)) :
    ∃ (K : Type (u + 1)) (_ : Finite K) (W : K → SmallEtale B S.obj S.property),
      Sieve.ofArrows W (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (W k)) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) ∧
      (∀ k, IsAffine (W k).obj.left.obj) ∧
      ∀ k, R ((SmallEtale.finalIsTerminal B S.obj S.property).from (W k)) := by
  let Dg : PUnit.{u + 1}ᵒᵖ ⥤ B.Scheme := (Functor.const _).obj S
  let c : Cone (Dg ⋙ B.inclusion) :=
    { pt := S.obj
      π := { app := fun _ => 𝟙 S.obj } }
  have hc : IsLimit c :=
    { lift := fun s => s.π.app (op PUnit.unit)
      fac := fun s j => by
        obtain rfl : j = op PUnit.unit := rfl
        exact Category.comp_id _
      uniq := fun s m hm => (Category.comp_id m).symm.trans (hm (op PUnit.unit)) }
  let T := SmallEtale.finalIsTerminal B S.obj S.property
  obtain ⟨j, -, K, hK, W, g, hcov, hWaff, href⟩ :=
    smallEtaleStagesCoveringsRefine_affine_of_isLimit B Dg c S.property hc
      (fun _ => by dsimp [Dg]; infer_instance) (fun _ => ‹_›) (fun _ => ‹_›) PUnit.unit
      (Σ W : SmallEtale B S.obj S.property, {f : W ⟶ SmallEtale.final B S.obj S.property // R f})
      (fun k => k.1) (fun k => k.2.1)
      ((SmallEtale.topology B S.obj S.property).superset_covering
        (fun W f hf => Sieve.ofArrows_mk _ (fun k : (Σ W : SmallEtale B S.obj S.property,
          {f : W ⟶ SmallEtale.final B S.obj S.property // R f}) => k.2.1) ⟨W, f, hf⟩) hR)
  refine ⟨K, hK, W, ?_, hWaff, fun k => ?_⟩
  · have e : g = fun k => T.from (W k) := funext fun k => T.hom_ext _ _
    subst e
    exact hcov
  · obtain ⟨m, ⟨d⟩⟩ := href k
    have hd : ((smallEtaleBaseChange_idIso B S).inv.app (W k) ≫ d) ≫ m.2.1 = T.from (W k) :=
      T.hom_ext _ _
    rw [← hd]
    exact R.downward_closed m.2.2 _

end Refine

section Inputs

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **Morphisms of constant sheaves with source satisfying `P` are locally constant.** For every
object `S` of the big étale site and every morphism `a` from the constant sheaf on `E` to the
constant sheaf on `E'` on the small étale site of `S`, with `P E`, there is a covering of the final
object on whose members the inverse image of `a` is a constant sheaf map. This is the form of
`AlgebraicGeometry.exists_cover_smallEtaleSheafPullback_map_eq` used here. -/
public def SmallEtaleConstantMapsLocallyConstant (P : A → Prop) : Prop :=
  ∀ (S : B.Scheme) {E E' : A}, P E →
    ∀ a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E',
    ∃ (K : Type (u + 1)) (V : K → SmallEtale B S.obj S.property),
      Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) ∧
      ∃ g : K → (E ⟶ E'), ∀ k,
        (smallEtaleSheafPullback B A (V k).obj.hom).map a =
          (smallEtaleConstantPullbackIso B A (V k).obj.hom E).hom ≫
            (constantSheaf (SmallEtale.topology B (V k).obj.left.obj (V k).obj.left.property)
              A).map (g k) ≫
            (smallEtaleConstantPullbackIso B A (V k).obj.hom E').inv

/-- **The constant sheaf functor is faithful over nonempty schemes**, the form of
`AlgebraicGeometry.smallEtale_constantSheaf_map_injective` used here. -/
public def SmallEtaleConstantFaithful : Prop :=
  ∀ (S : B.Scheme), Nonempty S.obj → ∀ {E E' : A} {g g' : E ⟶ E'},
    (constantSheaf (SmallEtale.topology B S.obj S.property) A).map g =
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).map g' → g = g'

/-- The underlying object of a member of a family of objects of the small étale site. -/
private abbrev smallEtaleMember {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k : K) : B.Scheme :=
  (V k).obj.left

/-- The structure morphism of a member of a family of objects of the small étale site. Named, so
that the kernel compares it syntactically with the family of étale morphisms of the gluing
statements. -/
private abbrev smallEtaleMemberHom {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k : K) : smallEtaleMember B V k ⟶ S :=
  (V k).obj.hom

/-- The structure morphism of a member is étale. -/
private instance etale_smallEtaleMemberHom {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k : K) :
    Etale (B.inclusion.map (smallEtaleMemberHom B V k)) :=
  (V k).property

/-- **Inverse images to the members of a covering are jointly faithful**: two morphisms of sheaves
on the small étale site of `S` with equal inverse images along the structure morphisms of the
members of a covering of the final object are equal. This is
`AlgebraicGeometry.smallEtaleSheafPullback_jointly_faithful` for the structure morphisms. -/
public theorem smallEtaleSheafPullback_jointly_faithful_members (S : B.Scheme) {K : Type*}
    (V : K → SmallEtale B S.obj S.property)
    (hV : Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) A} (ψ ψ' : F ⟶ G)
    (h : ∀ k, (smallEtaleSheafPullback B A (V k).obj.hom).map ψ =
      (smallEtaleSheafPullback B A (V k).obj.hom).map ψ') : ψ = ψ' :=
  smallEtaleSheafPullback_jointly_faithful B A S (smallEtaleMemberHom B V)
    (SmallEtaleGluing.sieve_ofEtaleHom_memberHom B S V hV) ψ ψ' h

/-- The overlap of two members of a family of objects of the small étale site, the fibre product
of their structure morphisms. Named, rather than written as a `fun`, so that the kernel does not
have to compare projections out of beta-redexes of fibre products. -/
private abbrev smallEtaleOverlap {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k l : K) : B.Scheme :=
  pullback (V k).obj.hom (V l).obj.hom

/-- The first projection of the overlap of two members. -/
private abbrev smallEtaleOverlapFst {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k l : K) :
    smallEtaleOverlap B V k l ⟶ smallEtaleMember B V k :=
  pullback.fst (V k).obj.hom (V l).obj.hom

/-- The second projection of the overlap of two members. -/
private abbrev smallEtaleOverlapSnd {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k l : K) :
    smallEtaleOverlap B V k l ⟶ smallEtaleMember B V l :=
  pullback.snd (V k).obj.hom (V l).obj.hom

/-- The structure morphism of the overlap of two members. -/
private abbrev smallEtaleOverlapHom {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k l : K) : smallEtaleOverlap B V k l ⟶ S :=
  pullback.fst (V k).obj.hom (V l).obj.hom ≫ (V k).obj.hom

/-- The overlap of two members is their fibre product. -/
private theorem isPullback_smallEtaleOverlap {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k l : K) :
    IsPullback (smallEtaleOverlapFst B V k l) (smallEtaleOverlapSnd B V k l)
      (smallEtaleMemberHom B V k) (smallEtaleMemberHom B V l) :=
  IsPullback.of_hasPullback _ _

/-- The first projection of the overlap followed by the structure morphism of the first member is
the structure morphism of the overlap. -/
private theorem smallEtaleOverlapFst_comp {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k l : K) :
    smallEtaleOverlapFst B V k l ≫ smallEtaleMemberHom B V k =
      smallEtaleOverlapHom B V k l :=
  rfl

/-- The second projection of the overlap followed by the structure morphism of the second member
is the structure morphism of the overlap. -/
private theorem smallEtaleOverlapSnd_comp {S : B.Scheme} {K : Type*}
    (V : K → SmallEtale B S.obj S.property) (k l : K) :
    smallEtaleOverlapSnd B V k l ≫ smallEtaleMemberHom B V l =
      smallEtaleOverlapHom B V k l :=
  pullback.condition.symm

/-- **Gluing of morphisms of constant sheaves along a covering**, in transported form: morphisms of
constant sheaves over the members of a covering of the final object whose transports to the
overlaps agree are the transports of a morphism of constant sheaves over `S`. This is
`AlgebraicGeometry.smallEtaleSheafPullback_exists_map_eq_of_isPullback` read through
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso'_conj_constantSheaf`. -/
public theorem exists_smallEtaleConstantTransport_eq_of_compatible
    (S : B.Scheme) {K : Type*}
    (V : K → SmallEtale B S.obj S.property)
    (hV : Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property)) {E E' : A}
    (b : ∀ k, (constantSheaf (SmallEtale.topology B (V k).obj.left.obj
        (V k).obj.left.property) A).obj E ⟶ (constantSheaf (SmallEtale.topology B
        (V k).obj.left.obj (V k).obj.left.property) A).obj E')
    (hb : ∀ k l,
      smallEtaleConstantTransport B A (pullback.fst (V k).obj.hom (V l).obj.hom) (b k) =
        smallEtaleConstantTransport B A (pullback.snd (V k).obj.hom (V l).obj.hom) (b l)) :
    ∃ b₀ : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
        (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E',
      ∀ k, smallEtaleConstantTransport B A (V k).obj.hom b₀ = b k := by
  obtain ⟨ψ, hψ⟩ := smallEtaleSheafPullback_exists_map_eq_of_isPullback B A S
    (smallEtaleMemberHom B V) (SmallEtaleGluing.sieve_ofEtaleHom_memberHom B S V hV)
    (smallEtaleOverlap B V) (smallEtaleOverlapFst B V) (smallEtaleOverlapSnd B V)
    (smallEtaleOverlapHom B V) (isPullback_smallEtaleOverlap B V) (smallEtaleOverlapFst_comp B V)
    (smallEtaleOverlapSnd_comp B V)
    (fun k => (smallEtaleConstantPullbackIso B A (smallEtaleMemberHom B V k) E).hom ≫
      b k ≫ (smallEtaleConstantPullbackIso B A (smallEtaleMemberHom B V k) E').inv)
    (fun k l => by
      rw [smallEtaleSheafPullbackCompIso'_conj_constantSheaf,
        smallEtaleSheafPullbackCompIso'_conj_constantSheaf]
      exact congrArg (fun x => _ ≫ x ≫ _) (hb k l))
  exact ⟨ψ, fun k => (smallEtaleSheafPullback_map_eq_iff B A _ ψ _).mp (hψ k)⟩

end Inputs

section Limit

variable (B : BigEtaleSite.{u}) {A : Type t} [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- Transport to a stage followed by transport to the vertex is transport to the vertex. -/
public theorem smallEtaleConstantTransport_coneStageHom_systemStageHom {i j : I} (hij : i ≤ j)
    {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
        A).obj E ⟶
      (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
        A).obj E') :
    smallEtaleConstantTransport B A (coneStageHom B Dg c hX j)
        (smallEtaleConstantTransport B A (systemStageHom B Dg hij) a) =
      smallEtaleConstantTransport B A (coneStageHom B Dg c hX i) a :=
  (smallEtaleConstantTransport_comp' B A _ _ _ (coneStageHom_comp B Dg c hX hij) a).symm

/-- Transport along two transition morphisms is transport along their composite. -/
public theorem smallEtaleConstantTransport_systemStageHom_trans {i j k : I} (hij : i ≤ j)
    (hjk : j ≤ k) {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
        A).obj E ⟶
      (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
        A).obj E') :
    smallEtaleConstantTransport B A (systemStageHom B Dg hjk)
        (smallEtaleConstantTransport B A (systemStageHom B Dg hij) a) =
      smallEtaleConstantTransport B A (systemStageHom B Dg (hij.trans hjk)) a :=
  (smallEtaleConstantTransport_comp' B A _ _ _ (systemStageHom_comp B Dg hij hjk) a).symm

/-- **Two constant maps which agree over the base change of a member to the limit agree, or the
base changes of the member to late stages are empty.** Let `W` be a quasi-compact,
quasi-separated object of the small étale site of `X_i`. If the constant sheaf maps attached to
`x` and `y` agree on `W ×_{X_i} X`, then `x = y` when `W ×_{X_i} X` is nonempty, and otherwise
the base changes `W ×_{X_i} X_j` are empty for all late `j` (Tag 05F3 for the member system of
`W`). -/
public theorem exists_stage_eq_or_isEmpty (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hinj : SmallEtaleConstantFaithful B A) (i : I)
    (W : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    [CompactSpace W.obj.left.obj] [QuasiSeparatedSpace W.obj.left.obj] {E E' : A}
    {x y : E ⟶ E'}
    (hxy : (constantSheaf (SmallEtale.topology B
        (pullback W.obj.hom (coneStageHom B Dg c hX i)).obj
        (pullback W.obj.hom (coneStageHom B Dg c hX i)).property) A).map x =
      (constantSheaf (SmallEtale.topology B
        (pullback W.obj.hom (coneStageHom B Dg c hX i)).obj
        (pullback W.obj.hom (coneStageHom B Dg c hX i)).property) A).map y) :
    ∃ j, i ≤ j ∧ (x = y ∨ ∀ j' (h : i ≤ j'), j ≤ j' →
      IsEmpty (pullback W.obj.hom (systemStageHom B Dg h)).obj) := by
  by_cases hne : Nonempty (pullback W.obj.hom (coneStageHom B Dg c hX i)).obj
  · exact ⟨i, le_rfl, Or.inl (hinj _ hne hxy)⟩
  · have he : IsEmpty (memberCone B Dg c hX i W).pt := not_nonempty_iff.mp hne
    obtain ⟨j, hj, hj'⟩ := exists_forall_isEmpty_stage_of_isEmpty B (memberSystem B Dg i W)
      (memberCone B Dg c hX i W) (memberConeIsLimit B Dg c hX i W hc)
      (memberSystem_isAffineHom haff) (memberSystem_compactSpace haff ‹_›)
      (memberSystem_quasiSeparatedSpace haff ‹_›) he ⟨i, le_rfl⟩
    exact ⟨j.1, j.2, Or.inr fun j' h hjj' => hj' ⟨j', h⟩ hjj'⟩

/-- **Morphisms of constant sheaves at a stage which agree at the limit agree at a later stage**,
for a coefficient category in which morphisms of constant sheaves with source satisfying `P` are
locally constant and the constant sheaf functor is faithful over nonempty schemes. Two morphisms
from the constant sheaf on `E` to the constant sheaf on `E'` on the small étale site of `X_i`,
with `P E`, whose transports to `X` agree have equal transports to some later stage.

Both are constant on a common finite affine covering of `X_i`; over each member the two values
agree, or the base changes of the member to late stages are empty
(`AlgebraicGeometry.exists_stage_eq_or_isEmpty`). At a stage beyond all members the transports
agree on the base change of the covering, hence agree. -/
public theorem exists_stage_transport_eq_of_transport_eq (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A)
    (i : I) {E E' : A} (hE : P E)
    (a b : (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
        A).obj E ⟶
      (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
        A).obj E')
    (hab : smallEtaleConstantTransport B A (coneStageHom B Dg c hX i) a =
      smallEtaleConstantTransport B A (coneStageHom B Dg c hX i) b) :
    ∃ j, ∃ hij : i ≤ j, smallEtaleConstantTransport B A (systemStageHom B Dg hij) a =
      smallEtaleConstantTransport B A (systemStageHom B Dg hij) b := by
  obtain ⟨Ka, Va, hVa, ga, hga⟩ := hloc _ hE a
  obtain ⟨Kb, Vb, hVb, gb, hgb⟩ := hloc _ hE b
  have hR := (SmallEtale.topology B (Dg.obj (op i)).obj
    (Dg.obj (op i)).property).intersection_covering
      (smallEtaleConstancySieve_mem B A a Va hVa ga hga)
      (smallEtaleConstancySieve_mem B A b Vb hVb gb hgb)
  have := hqc i
  have := hqs i
  obtain ⟨K, hK, W, hW, hWaff, hWR⟩ := exists_finite_affine_le_sieve B (Dg.obj (op i)) _ hR
  choose x hx using fun k => (hWR k).1
  choose y hy using fun k => (hWR k).2
  have hQ : ∀ k, (constantSheaf (SmallEtale.topology B
        (pullback (W k).obj.hom (coneStageHom B Dg c hX i)).obj
        (pullback (W k).obj.hom (coneStageHom B Dg c hX i)).property) A).map (x k) =
      (constantSheaf (SmallEtale.topology B
        (pullback (W k).obj.hom (coneStageHom B Dg c hX i)).obj
        (pullback (W k).obj.hom (coneStageHom B Dg c hX i)).property) A).map (y k) := by
    intro k
    have h1 := smallEtaleConstantTransport_eq_of_comp B A
      (pullback.fst (W k).obj.hom (coneStageHom B Dg c hX i)) (W k).obj.hom _ rfl (hx k)
    have h2 := smallEtaleConstantTransport_eq_of_comp B A
      (pullback.fst (W k).obj.hom (coneStageHom B Dg c hX i)) (W k).obj.hom _ rfl (hy k)
    rw [smallEtaleConstantTransport_comp' B A
      (pullback.snd (W k).obj.hom (coneStageHom B Dg c hX i)) (coneStageHom B Dg c hX i) _
      pullback.condition.symm] at h1 h2
    rw [← h1, ← h2, hab]
  have hst : ∀ k, ∃ j, i ≤ j ∧ (x k = y k ∨ ∀ j' (h : i ≤ j'), j ≤ j' →
      IsEmpty (pullback (W k).obj.hom (systemStageHom B Dg h)).obj) := fun k => by
    have := hWaff k
    exact exists_stage_eq_or_isEmpty B Dg c hX hc haff hinj i (W k) (hQ k)
  choose j hij hj using hst
  have : Nonempty I := ⟨i⟩
  obtain ⟨J, hJ⟩ := Finite.exists_le (fun o : Option K => o.elim i j)
  have hiJ : i ≤ J := hJ none
  refine ⟨J, hiJ, smallEtaleSheafPullback_jointly_faithful_members B A _
    (fun k => (smallEtaleBaseChange B (systemStageHom B Dg hiJ)).obj (W k))
    (smallEtale_sieve_ofArrows_final_baseChange B _ W _ hW) _ _ fun k =>
      smallEtaleSheafPullback_map_eq_of_transport_eq B A _ ?_⟩
  rw [smallEtaleConstantTransport_baseChange B A _ (W k) (hx k),
    smallEtaleConstantTransport_baseChange B A _ (W k) (hy k)]
  rcases hj k with h | h
  · rw [h]
  · have : IsEmpty ((smallEtaleBaseChange B (systemStageHom B Dg hiJ)).obj (W k)).obj.left.obj :=
      h J hiJ (hJ (some k))
    exact SmallEtale.sheaf_hom_ext_of_isEmpty B _ _ _ _

/-- **Two constant values of a map over the base changes of two members agree, or the overlaps of
the members are empty at late stages.** Let `W₁`, `W₂` be quasi-compact, quasi-separated objects
of the small étale site of the quasi-separated stage `X_j`, and let `a` be a morphism of constant
sheaves at `X` which is the constant map attached to `x₁` over `W₁ ×_{X_j} X` and to `x₂` over
`W₂ ×_{X_j} X`. Then `x₁ = x₂`, or the overlaps of the base changes of `W₁` and `W₂` to all late
stages are empty.

This is `AlgebraicGeometry.exists_stage_eq_or_isEmpty` for the overlap `W₁ ×_{X_j} W₂`, which is
quasi-compact and quasi-separated, and over whose base change to `X` both values are values of
`a`; the overlap at a later stage maps to the base change of that overlap. -/
public theorem exists_stage_eq_or_isEmpty_overlap (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hinj : SmallEtaleConstantFaithful B A) (j : I)
    [QuasiSeparatedSpace (Dg.obj (op j)).obj]
    (W₁ W₂ : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
    [CompactSpace W₁.obj.left.obj] [QuasiSeparatedSpace W₁.obj.left.obj]
    [CompactSpace W₂.obj.left.obj] [QuasiSeparatedSpace W₂.obj.left.obj] {E E' : A}
    {a : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj (B.obj c.pt hX).property)
        A).obj E ⟶
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj (B.obj c.pt hX).property)
        A).obj E'} {x₁ x₂ : E ⟶ E'}
    (h₁ : smallEtaleConstantTransport B A
      ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj W₁).obj.hom a =
      (constantSheaf (SmallEtale.topology B
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj W₁).obj.left.obj
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj W₁).obj.left.property)
        A).map x₁)
    (h₂ : smallEtaleConstantTransport B A
      ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj W₂).obj.hom a =
      (constantSheaf (SmallEtale.topology B
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj W₂).obj.left.obj
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj W₂).obj.left.property)
        A).map x₂) :
    ∃ J, j ≤ J ∧ (x₁ = x₂ ∨ ∀ J' (h : j ≤ J'), J ≤ J' →
      IsEmpty (pullback ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj W₁).obj.hom
        ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj W₂).obj.hom).obj) := by
  have : Etale (B.inclusion.map (pullback.fst W₁.obj.hom W₂.obj.hom)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback W₁.obj.hom W₂.obj.hom).map
      B.inclusion).flip W₂.property
  have : Etale (B.inclusion.map W₁.obj.hom) := W₁.property
  have : Etale (B.inclusion.map (pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom)) := by
    rw [B.inclusion.map_comp]
    infer_instance
  let O := SmallEtale.ofEtaleHom B (pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom)
  have : CompactSpace (B.inclusion.obj W₂.obj.left) := ‹CompactSpace W₂.obj.left.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj W₂.obj.left) :=
    ‹QuasiSeparatedSpace W₂.obj.left.obj›
  have : CompactSpace (B.inclusion.obj W₁.obj.left) := ‹CompactSpace W₁.obj.left.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj W₁.obj.left) :=
    ‹QuasiSeparatedSpace W₁.obj.left.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj (Dg.obj (op j))) :=
    ‹QuasiSeparatedSpace (Dg.obj (op j)).obj›
  have : QuasiCompact (B.inclusion.map (pullback.fst W₁.obj.hom W₂.obj.hom)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback W₁.obj.hom W₂.obj.hom).map
      B.inclusion).flip (inferInstance : QuasiCompact (B.inclusion.map W₂.obj.hom))
  have : QuasiSeparated (B.inclusion.map (pullback.fst W₁.obj.hom W₂.obj.hom)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback W₁.obj.hom W₂.obj.hom).map
      B.inclusion).flip (inferInstance : QuasiSeparated (B.inclusion.map W₂.obj.hom))
  have : CompactSpace O.obj.left.obj :=
    QuasiCompact.compactSpace_of_compactSpace
      (B.inclusion.map (pullback.fst W₁.obj.hom W₂.obj.hom))
  have : QuasiSeparatedSpace O.obj.left.obj :=
    quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map (pullback.fst W₁.obj.hom W₂.obj.hom))
  -- the two values agree over the base change of the overlap to the limit
  have hO : O.obj.hom = pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom := rfl
  have hZ := pullback.condition (f := O.obj.hom) (g := coneStageHom B Dg c hX j)
  rw [hO] at hZ
  let l₁ := pullback.lift (f := W₁.obj.hom) (g := coneStageHom B Dg c hX j)
    (pullback.fst O.obj.hom (coneStageHom B Dg c hX j) ≫
      pullback.fst W₁.obj.hom W₂.obj.hom) (pullback.snd O.obj.hom (coneStageHom B Dg c hX j))
    (by rw [Category.assoc]; exact hZ)
  let l₂ := pullback.lift (f := W₂.obj.hom) (g := coneStageHom B Dg c hX j)
    (pullback.fst O.obj.hom (coneStageHom B Dg c hX j) ≫
      pullback.snd W₁.obj.hom W₂.obj.hom) (pullback.snd O.obj.hom (coneStageHom B Dg c hX j))
    (by rw [Category.assoc, ← pullback.condition]; exact hZ)
  have e₁ := smallEtaleConstantTransport_eq_of_comp B A l₁ _ _ (pullback.lift_snd _ _ _) h₁
  have e₂ := smallEtaleConstantTransport_eq_of_comp B A l₂ _ _ (pullback.lift_snd _ _ _) h₂
  obtain ⟨J, hjJ, hJ⟩ := exists_stage_eq_or_isEmpty B Dg c hX hc haff hinj j O (e₁.symm.trans e₂)
  refine ⟨J, hjJ, hJ.imp_right fun hJ J' h hJJ' => ?_⟩
  have hE := hJ J' h hJJ'
  let t := systemStageHom B Dg h
  let Q₁ : pullback ((smallEtaleBaseChange B t).obj W₁).obj.hom
      ((smallEtaleBaseChange B t).obj W₂).obj.hom ⟶ pullback W₁.obj.hom t :=
    pullback.fst ((smallEtaleBaseChange B t).obj W₁).obj.hom
      ((smallEtaleBaseChange B t).obj W₂).obj.hom
  let Q₂ : pullback ((smallEtaleBaseChange B t).obj W₁).obj.hom
      ((smallEtaleBaseChange B t).obj W₂).obj.hom ⟶ pullback W₂.obj.hom t :=
    pullback.snd ((smallEtaleBaseChange B t).obj W₁).obj.hom
      ((smallEtaleBaseChange B t).obj W₂).obj.hom
  have hQ : Q₁ ≫ pullback.snd W₁.obj.hom t = Q₂ ≫ pullback.snd W₂.obj.hom t := pullback.condition
  let φ := pullback.lift (f := O.obj.hom) (g := t)
    (pullback.lift (Q₁ ≫ pullback.fst W₁.obj.hom t) (Q₂ ≫ pullback.fst W₂.obj.hom t)
      (by rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition,
        reassoc_of% hQ]))
    (Q₁ ≫ pullback.snd W₁.obj.hom t)
    (by rw [hO, pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])
  exact ⟨fun q => hE.elim ((B.inclusion.map φ).base q)⟩

/-- **Morphisms of constant sheaves at the limit come from a stage**, for a coefficient category
in which morphisms of constant sheaves with source satisfying `P` are locally constant and the
constant sheaf functor is faithful over nonempty schemes. Every morphism from the constant sheaf
on `E` to the constant sheaf on `E'` on the small étale site of `X`, with `P E`, is the transport
of a morphism at some stage beyond a given one.

The morphism is constant on the base change of a finite affine covering `{W_n}` of a stage
(Tag 0EYL). Over overlaps `W_n ×_{X_j} W_m` the two values agree, or the base changes of the
overlap to late stages are empty (`AlgebraicGeometry.exists_stage_eq_or_isEmpty_overlap`); so at a
late stage the constant maps on the base changes of the `W_n` glue, and the glued morphism has the
given transport, as both are constant with the same values on a covering of `X`. -/
public theorem exists_stage_transport_eq (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A)
    {E E' : A} (hE : P E)
    (a : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj (B.obj c.pt hX).property)
        A).obj E ⟶
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj (B.obj c.pt hX).property)
        A).obj E') (i : I) :
    ∃ j, i ≤ j ∧ ∃ b : (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) A).obj E ⟶
        (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) A).obj E',
      smallEtaleConstantTransport B A (coneStageHom B Dg c hX j) b = a := by
  have : Nonempty I := ⟨i⟩
  obtain ⟨K, V, hV, g, hg⟩ := hloc (B.obj c.pt hX) hE a
  obtain ⟨j, hij, K', hK', W, w, hW, hWaff, href⟩ :=
    smallEtaleStagesCoveringsRefine_affine_of_isLimit B Dg c hX hc haff hqc hqs i K V _ hV
  -- the value of `a` over the base change of each member
  have hval : ∀ n, ∃ x : E ⟶ E', smallEtaleConstantTransport B A
      ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj (W n)).obj.hom a =
      (constantSheaf (SmallEtale.topology B
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj (W n)).obj.left.obj
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj (W n)).obj.left.property)
        A).map x := by
    intro n
    obtain ⟨m, ⟨q⟩⟩ := href n
    exact ⟨g m, smallEtaleConstantTransport_eq_of_comp B A q.hom.left (V m).obj.hom _
      (Over.w q.hom) ((smallEtaleSheafPullback_map_eq_iff B A _ a _).mp (hg m))⟩
  choose x hx using hval
  have := hqs j
  have hst : ∀ p : K' × K', ∃ J, j ≤ J ∧ (x p.1 = x p.2 ∨ ∀ J' (h : j ≤ J'), J ≤ J' →
      IsEmpty (pullback ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj (W p.1)).obj.hom
        ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj (W p.2)).obj.hom).obj) := by
    intro p
    have := hWaff p.1
    have := hWaff p.2
    exact exists_stage_eq_or_isEmpty_overlap B Dg c hX hc haff hinj j (W p.1) (W p.2)
      (hx p.1) (hx p.2)
  choose J hJ hJ' using hst
  obtain ⟨M, hM⟩ := Finite.exists_le (fun o : Option (K' × K') => o.elim j J)
  have hjM : j ≤ M := hM none
  let t := systemStageHom B Dg hjM
  let U := fun n => (smallEtaleBaseChange B t).obj (W n)
  have hW' : Sieve.ofArrows W (fun n => (SmallEtale.finalIsTerminal B (Dg.obj (op j)).obj
      (Dg.obj (op j)).property).from (W n)) ∈ SmallEtale.topology B (Dg.obj (op j)).obj
        (Dg.obj (op j)).property (SmallEtale.final B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) := by
    have e : w = fun n => (SmallEtale.finalIsTerminal B (Dg.obj (op j)).obj
        (Dg.obj (op j)).property).from (W n) :=
      funext fun n => (SmallEtale.finalIsTerminal B _ _).hom_ext _ _
    exact e ▸ hW
  have hU := smallEtale_sieve_ofArrows_final_baseChange B t W _ hW'
  obtain ⟨b, hb⟩ := exists_smallEtaleConstantTransport_eq_of_compatible B A _ U hU
    (fun n => (constantSheaf (SmallEtale.topology B (U n).obj.left.obj (U n).obj.left.property)
      A).map (x n)) (fun k l => by
    simp only [smallEtaleConstantTransport_constantSheaf_map]
    rcases hJ' (k, l) with h | h
    · rw [h]
    · have : IsEmpty (pullback (U k).obj.hom (U l).obj.hom).obj := h M hjM (hM (some (k, l)))
      exact SmallEtale.sheaf_hom_ext_of_isEmpty B _ _ _ _)
  refine ⟨M, hij.trans hjM, b, smallEtaleSheafPullback_jointly_faithful_members B A (B.obj c.pt hX)
    (fun n => (smallEtaleBaseChange B (coneStageHom B Dg c hX M)).obj (U n))
    (smallEtale_sieve_ofArrows_final_baseChange B _ U _ hU) _ _ fun n =>
      smallEtaleSheafPullback_map_eq_of_transport_eq B A _ ?_⟩
  rw [smallEtaleConstantTransport_baseChange B A _ (U n) (hb n)]
  let p₁ : pullback (U n).obj.hom (coneStageHom B Dg c hX M) ⟶ pullback (W n).obj.hom t :=
    pullback.fst (U n).obj.hom (coneStageHom B Dg c hX M)
  have h₁ : p₁ ≫ pullback.snd (W n).obj.hom t =
      pullback.snd (U n).obj.hom (coneStageHom B Dg c hX M) ≫ coneStageHom B Dg c hX M :=
    pullback.condition
  have h₂ : pullback.fst (W n).obj.hom t ≫ (W n).obj.hom = pullback.snd (W n).obj.hom t ≫ t :=
    pullback.condition
  let φ := pullback.lift (f := (W n).obj.hom) (g := coneStageHom B Dg c hX j)
    (p₁ ≫ pullback.fst (W n).obj.hom t)
    (pullback.snd (U n).obj.hom (coneStageHom B Dg c hX M))
    (by rw [Category.assoc, h₂, reassoc_of% h₁, coneStageHom_comp])
  exact (smallEtaleConstantTransport_eq_of_comp B A φ _ _ (pullback.lift_snd _ _ _) (hx n)).symm

/-- **Isomorphisms of constant sheaves at the limit come from a stage**, for a coefficient
category as in `AlgebraicGeometry.exists_stage_transport_eq`. Every isomorphism between the
constant sheaves on `E` and on `E'` on the small étale site of `X`, with `P E` and `P E'`, is the
transport of an isomorphism at some stage beyond a given one: its two components come from a stage
(`AlgebraicGeometry.exists_stage_transport_eq`), and the two composites become identities at a
later stage (`AlgebraicGeometry.exists_stage_transport_eq_of_transport_eq`). -/
public theorem exists_stage_transport_iso (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A)
    {E E' : A} (hE : P E) (hE' : P E')
    (e : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj (B.obj c.pt hX).property)
        A).obj E ≅
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj (B.obj c.pt hX).property)
        A).obj E') (i : I) :
    ∃ j, i ≤ j ∧ ∃ e₀ : (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) A).obj E ≅
        (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) A).obj E',
      smallEtaleConstantTransport B A (coneStageHom B Dg c hX j) e₀.hom = e.hom := by
  obtain ⟨j₁, hij₁, b₁, hb₁⟩ :=
    exists_stage_transport_eq B Dg c hX hc haff hqc hqs P hloc hinj hE e.hom i
  obtain ⟨j₂, hj₁₂, b₂, hb₂⟩ :=
    exists_stage_transport_eq B Dg c hX hc haff hqc hqs P hloc hinj hE' e.inv j₁
  set b₁' := smallEtaleConstantTransport B A (systemStageHom B Dg hj₁₂) b₁ with hb₁'def
  have hb₁' : smallEtaleConstantTransport B A (coneStageHom B Dg c hX j₂) b₁' = e.hom := by
    rw [hb₁'def, smallEtaleConstantTransport_coneStageHom_systemStageHom, hb₁]
  obtain ⟨j₃, hj₂₃, h₃⟩ := exists_stage_transport_eq_of_transport_eq B Dg c hX hc haff hqc hqs
    P hloc hinj j₂ hE (b₁' ≫ b₂) (𝟙 _) (by simp [hb₁', hb₂])
  obtain ⟨j₄, hj₂₄, h₄⟩ := exists_stage_transport_eq_of_transport_eq B Dg c hX hc haff hqc hqs
    P hloc hinj j₂ hE' (b₂ ≫ b₁') (𝟙 _) (by simp [hb₁', hb₂])
  obtain ⟨j₅, hj₃₅, hj₄₅⟩ := directed_of (· ≤ ·) j₃ j₄
  have hj₂₅ : j₂ ≤ j₅ := hj₂₃.trans hj₃₅
  have k₃ := congrArg (smallEtaleConstantTransport B A (systemStageHom B Dg hj₃₅)) h₃
  have k₄ := congrArg (smallEtaleConstantTransport B A (systemStageHom B Dg hj₄₅)) h₄
  simp only [smallEtaleConstantTransport_systemStageHom_trans,
    smallEtaleConstantTransport_comp, smallEtaleConstantTransport_id] at k₃ k₄
  refine ⟨j₅, (hij₁.trans hj₁₂).trans hj₂₅,
    { hom := smallEtaleConstantTransport B A (systemStageHom B Dg hj₂₅) b₁'
      inv := smallEtaleConstantTransport B A (systemStageHom B Dg hj₂₅) b₂
      hom_inv_id := k₃
      inv_hom_id := k₄ }, ?_⟩
  rw [smallEtaleConstantTransport_coneStageHom_systemStageHom, hb₁']

end Limit

section Instances

variable (B : BigEtaleSite.{u})

attribute [local instance] SmallEtale.isRightAdjointPushforward_type
  SmallEtale.isRightAdjointPushforward_addCommGrpCat
  SmallEtale.isRightAdjointPushforward_moduleCat_site

/-- Morphisms of constant sheaves of sets with finite source are locally constant. -/
public theorem smallEtaleConstantMapsLocallyConstant_type :
    SmallEtaleConstantMapsLocallyConstant B (Type (u + 1)) (fun E => Finite E) :=
  fun S _ _ hE a => by
    have := hE
    exact exists_cover_smallEtaleSheafPullback_map_eq_type B S a

/-- Morphisms of constant abelian sheaves with finite source are locally constant. -/
public theorem smallEtaleConstantMapsLocallyConstant_addCommGrpCat :
    SmallEtaleConstantMapsLocallyConstant B AddCommGrpCat.{u + 1} (fun E => Finite E) :=
  fun S _ _ hE a => by
    have := hE
    exact exists_cover_smallEtaleSheafPullback_map_eq_addCommGrpCat B S a

/-- Morphisms of constant sheaves of modules with finitely generated source are locally
constant. -/
public theorem smallEtaleConstantMapsLocallyConstant_moduleCat (Λ : Type (u + 1)) [CommRing Λ] :
    SmallEtaleConstantMapsLocallyConstant B (ModuleCat.{u + 1} Λ)
      (fun E => Module.Finite Λ E) :=
  fun S _ _ hE a => by
    have := hE
    exact exists_cover_smallEtaleSheafPullback_map_eq_moduleCat B S Λ a

/-- Constant sheaves of sets are faithful over nonempty schemes. -/
public theorem smallEtaleConstantFaithful_type : SmallEtaleConstantFaithful B (Type (u + 1)) :=
  fun S hne _ _ _ _ h => smallEtale_constantSheaf_map_injective_type B S hne h

/-- Constant abelian sheaves are faithful over nonempty schemes. -/
public theorem smallEtaleConstantFaithful_addCommGrpCat :
    SmallEtaleConstantFaithful B AddCommGrpCat.{u + 1} :=
  fun S hne _ _ _ _ h => smallEtale_constantSheaf_map_injective_addCommGrpCat B S hne h

/-- Constant sheaves of modules are faithful over nonempty schemes. -/
public theorem smallEtaleConstantFaithful_moduleCat (Λ : Type (u + 1)) [CommRing Λ] :
    SmallEtaleConstantFaithful B (ModuleCat.{u + 1} Λ) :=
  fun S hne _ _ _ _ h => smallEtale_constantSheaf_map_injective_moduleCat B S hne Λ h

end Instances

section Concrete

attribute [local instance] SmallEtale.isRightAdjointPushforward_type
  SmallEtale.isRightAdjointPushforward_addCommGrpCat
  SmallEtale.isRightAdjointPushforward_moduleCat_site

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Morphisms of constant sheaves of sets at a stage which agree at the limit agree at a
later stage.** For `E` finite, two morphisms from the constant sheaf on `E` to the constant
sheaf on `E'` on the small étale site of `X_i` whose transports to `X` agree have equal transports
to some later stage. -/
public theorem exists_stage_transport_eq_of_transport_eq_type
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (i : I) {E E' : Type (u + 1)} [Finite E]
    (a b : (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property) (Type (u + 1))).obj E ⟶
      (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property) (Type (u + 1))).obj E')
    (hab : smallEtaleConstantTransport B (Type (u + 1)) (coneStageHom B Dg c hX i) a =
      smallEtaleConstantTransport B (Type (u + 1)) (coneStageHom B Dg c hX i) b) :
    ∃ j, ∃ hij : i ≤ j,
      smallEtaleConstantTransport B (Type (u + 1)) (systemStageHom B Dg hij) a =
        smallEtaleConstantTransport B (Type (u + 1)) (systemStageHom B Dg hij) b :=
  exists_stage_transport_eq_of_transport_eq B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_type B)
    (smallEtaleConstantFaithful_type B) i ‹_› a b hab

/-- **Morphisms of constant sheaves of sets at the limit come from a stage.** For `E`
finite, every morphism from the constant sheaf on `E` to the constant sheaf on `E'` on the
small étale site of `X` is the transport of a morphism at some stage beyond a given one. -/
public theorem exists_stage_transport_eq_type
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    {E E' : Type (u + 1)} [Finite E]
    (a : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) (Type (u + 1))).obj E ⟶
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) (Type (u + 1))).obj E')
    (i : I) :
    ∃ j, i ≤ j ∧ ∃ b : (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) (Type (u + 1))).obj E ⟶
        (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) (Type (u + 1))).obj E',
      smallEtaleConstantTransport B (Type (u + 1)) (coneStageHom B Dg c hX j) b = a :=
  exists_stage_transport_eq B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_type B)
    (smallEtaleConstantFaithful_type B) ‹_› a i

/-- **Isomorphisms of constant sheaves of sets at the limit come from a stage.** For `E`
and `E'` finite, every isomorphism between the constant sheaves on `E` and on `E'` on the
small étale site of `X` is the transport of an isomorphism at some stage beyond a given one. -/
public theorem exists_stage_transport_iso_type
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    {E E' : Type (u + 1)} [Finite E] [Finite E']
    (e : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) (Type (u + 1))).obj E ≅
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) (Type (u + 1))).obj E')
    (i : I) :
    ∃ j, i ≤ j ∧ ∃ e₀ : (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) (Type (u + 1))).obj E ≅
        (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) (Type (u + 1))).obj E',
      smallEtaleConstantTransport B (Type (u + 1)) (coneStageHom B Dg c hX j) e₀.hom =
        e.hom :=
  exists_stage_transport_iso B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_type B)
    (smallEtaleConstantFaithful_type B) ‹_› ‹_› e i

/-- **Morphisms of constant sheaves of abelian groups at a stage which agree at the limit agree at
a later stage.** For `E` finite, two morphisms from the constant sheaf on `E` to the constant sheaf
on `E'` on the small étale site of `X_i` whose transports to `X` agree have equal transports to
some later stage. -/
public theorem exists_stage_transport_eq_of_transport_eq_addCommGrpCat
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (i : I) {E E' : AddCommGrpCat.{u + 1}} [Finite E]
    (a b : (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property) AddCommGrpCat.{u + 1}).obj E ⟶
      (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property) AddCommGrpCat.{u + 1}).obj E')
    (hab : smallEtaleConstantTransport B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX i) a =
      smallEtaleConstantTransport B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX i) b) :
    ∃ j, ∃ hij : i ≤ j,
      smallEtaleConstantTransport B AddCommGrpCat.{u + 1} (systemStageHom B Dg hij) a =
        smallEtaleConstantTransport B AddCommGrpCat.{u + 1} (systemStageHom B Dg hij) b :=
  exists_stage_transport_eq_of_transport_eq B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_addCommGrpCat B)
    (smallEtaleConstantFaithful_addCommGrpCat B) i ‹_› a b hab

/-- **Morphisms of constant sheaves of abelian groups at the limit come from a stage.** For `E`
finite, every morphism from the constant sheaf on `E` to the constant sheaf on `E'` on the
small étale site of `X` is the transport of a morphism at some stage beyond a given one. -/
public theorem exists_stage_transport_eq_addCommGrpCat
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    {E E' : AddCommGrpCat.{u + 1}} [Finite E]
    (a : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) AddCommGrpCat.{u + 1}).obj E ⟶
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) AddCommGrpCat.{u + 1}).obj E')
    (i : I) :
    ∃ j, i ≤ j ∧ ∃ b : (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) AddCommGrpCat.{u + 1}).obj E ⟶
        (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) AddCommGrpCat.{u + 1}).obj E',
      smallEtaleConstantTransport B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX j) b = a :=
  exists_stage_transport_eq B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_addCommGrpCat B)
    (smallEtaleConstantFaithful_addCommGrpCat B) ‹_› a i

/-- **Isomorphisms of constant sheaves of abelian groups at the limit come from a stage.** For `E`
and `E'` finite, every isomorphism between the constant sheaves on `E` and on `E'` on the
small étale site of `X` is the transport of an isomorphism at some stage beyond a given one. -/
public theorem exists_stage_transport_iso_addCommGrpCat
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    {E E' : AddCommGrpCat.{u + 1}} [Finite E] [Finite E']
    (e : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) AddCommGrpCat.{u + 1}).obj E ≅
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) AddCommGrpCat.{u + 1}).obj E')
    (i : I) :
    ∃ j, i ≤ j ∧ ∃ e₀ : (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) AddCommGrpCat.{u + 1}).obj E ≅
        (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) AddCommGrpCat.{u + 1}).obj E',
      smallEtaleConstantTransport B AddCommGrpCat.{u + 1} (coneStageHom B Dg c hX j) e₀.hom =
        e.hom :=
  exists_stage_transport_iso B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_addCommGrpCat B)
    (smallEtaleConstantFaithful_addCommGrpCat B) ‹_› ‹_› e i

/-- **Morphisms of constant sheaves of modules at a stage which agree at the limit agree at a
later stage.** For `E` finitely generated, two morphisms from the constant sheaf on `E` to the
constant sheaf on `E'` on the small étale site of `X_i` whose transports to `X` agree have equal
transports to some later stage. -/
public theorem exists_stage_transport_eq_of_transport_eq_moduleCat
    (Λ : Type (u + 1)) [CommRing Λ]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (i : I) {E E' : ModuleCat.{u + 1} Λ} [Module.Finite Λ E]
    (a b : (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property) (ModuleCat.{u + 1} Λ)).obj E ⟶
      (constantSheaf (SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property) (ModuleCat.{u + 1} Λ)).obj E')
    (hab : smallEtaleConstantTransport B (ModuleCat.{u + 1} Λ) (coneStageHom B Dg c hX i) a =
      smallEtaleConstantTransport B (ModuleCat.{u + 1} Λ) (coneStageHom B Dg c hX i) b) :
    ∃ j, ∃ hij : i ≤ j,
      smallEtaleConstantTransport B (ModuleCat.{u + 1} Λ) (systemStageHom B Dg hij) a =
        smallEtaleConstantTransport B (ModuleCat.{u + 1} Λ) (systemStageHom B Dg hij) b :=
  exists_stage_transport_eq_of_transport_eq B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_moduleCat B Λ)
    (smallEtaleConstantFaithful_moduleCat B Λ) i ‹_› a b hab

/-- **Morphisms of constant sheaves of modules at the limit come from a stage.** For `E`
finitely generated, every morphism from the constant sheaf on `E` to the constant sheaf on `E'` on
the small étale site of `X` is the transport of a morphism at some stage beyond a given one. -/
public theorem exists_stage_transport_eq_moduleCat
    (Λ : Type (u + 1)) [CommRing Λ]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    {E E' : ModuleCat.{u + 1} Λ} [Module.Finite Λ E]
    (a : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) (ModuleCat.{u + 1} Λ)).obj E ⟶
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) (ModuleCat.{u + 1} Λ)).obj E')
    (i : I) :
    ∃ j, i ≤ j ∧ ∃ b : (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) (ModuleCat.{u + 1} Λ)).obj E ⟶
        (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) (ModuleCat.{u + 1} Λ)).obj E',
      smallEtaleConstantTransport B (ModuleCat.{u + 1} Λ) (coneStageHom B Dg c hX j) b = a :=
  exists_stage_transport_eq B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_moduleCat B Λ)
    (smallEtaleConstantFaithful_moduleCat B Λ) ‹_› a i

/-- **Isomorphisms of constant sheaves of modules at the limit come from a stage.** For `E`
and `E'` finitely generated, every isomorphism between the constant sheaves on `E` and on `E'` on
the small étale site of `X` is the transport of an isomorphism at some stage beyond a given one. -/
public theorem exists_stage_transport_iso_moduleCat
    (Λ : Type (u + 1)) [CommRing Λ]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    {E E' : ModuleCat.{u + 1} Λ} [Module.Finite Λ E] [Module.Finite Λ E']
    (e : (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) (ModuleCat.{u + 1} Λ)).obj E ≅
      (constantSheaf (SmallEtale.topology B (B.obj c.pt hX).obj
        (B.obj c.pt hX).property) (ModuleCat.{u + 1} Λ)).obj E')
    (i : I) :
    ∃ j, i ≤ j ∧ ∃ e₀ : (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) (ModuleCat.{u + 1} Λ)).obj E ≅
        (constantSheaf (SmallEtale.topology B (Dg.obj (op j)).obj
          (Dg.obj (op j)).property) (ModuleCat.{u + 1} Λ)).obj E',
      smallEtaleConstantTransport B (ModuleCat.{u + 1} Λ) (coneStageHom B Dg c hX j) e₀.hom =
        e.hom :=
  exists_stage_transport_iso B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_moduleCat B Λ)
    (smallEtaleConstantFaithful_moduleCat B Λ) ‹_› ‹_› e i

end Concrete

end AlgebraicGeometry

end
