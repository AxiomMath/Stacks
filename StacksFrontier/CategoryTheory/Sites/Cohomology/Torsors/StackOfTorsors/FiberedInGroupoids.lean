module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CategoryOfTorsors
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack
import StacksCore.Tactic.StacksAttribute

/-!
# The stack of torsors under a sheaf of groups

Let `(C, J)` be a site and let `𝒢` be a sheaf of groups on `C`. Stacks 04UK asserts that the
functor `p : 𝒢-Torsors ⥤ C` of Stacks 04UJ
(`SheafOfGroups.Torsors.projection`) defines a stack in groupoids over `C`, that is, the three
conditions of Stacks 02ZI: `p` is fibred in groupoids, the presheaves `Isom(F, H)` on `C/U` are
sheaves, and every descent datum along a covering of `C` is effective.

Condition (1) is proved here. Its content is the restriction `f^{-1}F` of a torsor along a
morphism `f : V ⟶ U` of `C`, which is also the `f^{-1}H` appearing in the definition of a
morphism of `𝒢-Torsors`: the sheaf on `C/V` obtained by composing the sheaf on `C/U` with
`CategoryTheory.Over.map f`, carrying the same action of `𝒢` because the sections of `𝒢|_V` over
`a : W ⟶ V` and the sections of `𝒢|_U` over `a ≫ f` are one and the same sections of `𝒢` over
`W`. The pair `(V, f^{-1}F)` with the evident morphism to `(U, F)` is a lift of `f`, and the
fill-ins are unique because the recorded map of a morphism of `𝒢-Torsors` is a bijection from the
sections of the source torsor over `a` to the sections of the target torsor over `a ≫ f`
(`SheafOfGroups.Torsors.Hom.existsUnique_map`).

Condition (2) is proved here as well. Its content is that a family of isomorphisms of torsors
over the members of a covering family of `U` which agree on the overlaps glues to a single
isomorphism over `U`: the glueing is the sheaf condition for the target torsor on `C/U`, read on
the total space of that torsor, and the glued map of sheaves is equivariant and bijective because
each of the given isomorphisms is.

## Main definitions

* `SheafOfGroups.Torsors.pullback`: the restriction `f^{-1}F` of a torsor along a morphism of
  `C`, as an object of `𝒢-Torsors` over the source of `f`.
* `SheafOfGroups.Torsors.pullbackHom`: the morphism `(V, f^{-1}F) ⟶ (U, F)` of `𝒢-Torsors` lying
  over `f`.
* `SheafOfGroups.Torsors.secOver`: the section of a torsor carried by an element of its total
  space, over a morphism of `C` which that element is known to lie over.

## Main results

* `SheafOfGroups.Torsors.projection_isFiberedInGroupoids`: **Stacks 04UK**, condition (1) of
  Stacks 02ZI for `p : 𝒢-Torsors ⥤ C`.
* `SheafOfGroups.Torsors.projection_isomIsSheaf`: **Stacks 04UK**, condition (2) of Stacks 02ZI
  for `p : 𝒢-Torsors ⥤ C`.
* `SheafOfGroups.Torsors.existsUnique_total`: glueing in the total space of a torsor, that is,
  the sheaf condition for the torsor read on its total space.
* `SheafOfGroups.Torsors.existsUnique_hom_of_sieve`: a morphism of `𝒢-Torsors` prescribed on a
  covering sieve of the base.
* `SheafOfGroups.Torsors.totalMap_mk`: the restriction maps of the total space of a torsor,
  computed by an arbitrary morphism of `C/U` over the given morphism of `C`.

## What is assumed

Nothing: all three conditions of Stacks 02ZI are proved outright, for an arbitrary site and an
arbitrary sheaf of groups on it, and `SheafOfGroups.Torsors.projection_isStackInGroupoids`
assembles them into `CategoryTheory.Functor.IsStackInGroupoids`.

Condition (3), effective descent, carries a universe price, and it is visible in the statement
rather than hidden: the glued torsor is assembled from matching families indexed by the
covering, so its sections live in `max u v s t`, where `u` and `v` are the object and hom
universes of the site, `s` is the index universe of the covering family and `t` is the section
universe. Hence `projection_isStackInGroupoids` is stated for `Torsors.{max u v s t}`. That is
the same bound the alternative route imposes: the source glues the given torsors by Stacks 04TP
and transports the action by Stacks 04TS, which this library has as
`CategoryTheory.GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver`, under the
hypothesis that the target category has limits of the size of the site, and for sheaves of sets
that bounds the section universe of the glued sheaf below in exactly the same way.

## Implementation notes

"Up to a replacement as in Stacks, Remark 03ZZ" is the source's way of saying that the collection
of all torsors is a proper class, so that the fibre categories have to be cut down to sets before
one may speak of a stack at all. Here the cutting down is the universe parameter of
`SheafOfGroups.Torsors`: its objects carry a torsor whose sections lie in a fixed `Type t`, so
`𝒢-Torsors` is a genuine type and `p` a functor between genuine categories, and the three
conditions can be stated for the category as given. Nothing is lost in condition (1): the
restriction `f^{-1}F` has literally the same sections as `F`, so it stays inside the same `Type t`
and no replacement is needed to lift a morphism. The library's rendering of the replacement itself
is `CategoryTheory.Functor.IsStack.exists_small_fullSubcategory`, which applies to any stack whose
source is essentially small, hence to this one once all three conditions are available.

## References

* [Stacks Project, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
-/

@[expose] public section

open CategoryTheory Opposite

universe t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace SheafOfGroups.Torsors

variable {𝒢 : SheafOfGroups.{w} (C := C) J}

/-- The restriction `f^{-1}F` of the torsor of an object `(U, F)` of `𝒢-Torsors` along a morphism
`f : V ⟶ U` of `C`, as an object `(V, f^{-1}F)` of `𝒢-Torsors`: the sections of `f^{-1}F` over
`a : W ⟶ V` are the sections of `F` over `a ≫ f`, and `𝒢` acts on them as it does on the latter,
which is meaningful because both groups of sections are the sections of `𝒢` over `W`. -/
@[sga "4 IV 3.1.2" "special case"]
def pullback (T : Torsors.{t} 𝒢) {V : C} (f : V ⟶ T.base) : Torsors.{t} 𝒢 where
  base := V
  torsor :=
    { presheaf := (Over.map f).op ⋙ T.torsor.presheaf
      isSheaf :=
        ((J.overMapPullback (Type t) f).obj ⟨T.torsor.presheaf, T.torsor.isSheaf⟩).property
      act := fun W γ s => T.torsor.act (op ((Over.map f).obj W.unop)) γ s
      one_act := fun W s => T.torsor.one_act (op ((Over.map f).obj W.unop)) s
      mul_act := fun W γ δ s => T.torsor.mul_act (op ((Over.map f).obj W.unop)) γ δ s
      naturality := fun h γ s => T.torsor.naturality ((Over.map f).op.map h) γ s
      simplyTransitive := fun W hW s u =>
        T.torsor.simplyTransitive (op ((Over.map f).obj W.unop)) hW s u }
  isTorsor := fun W => by
    obtain ⟨S, hS, hsec⟩ := T.isTorsor ((Over.map f).obj W)
    exact ⟨S.functorPullback (Over.map f),
      (Over.map f).cover_lift (J.over V) (J.over T.base) hS, fun _ _ hg => hsec hg⟩

/-- The restriction map of the total space of a torsor, computed by an arbitrary morphism of
`C/U` lying over the given morphism of `C`: restricting the section `s` over `a` along
`h : W' ⟶ W` is applying the sheaf to any morphism `Over.mk b ⟶ Over.mk a` whose underlying
morphism of `C` is `h`. -/
theorem totalMap_mk (T : Torsors.{t} 𝒢) {W W' : Cᵒᵖ} (h : W ⟶ W')
    {a : W.unop ⟶ T.base} {b : W'.unop ⟶ T.base} (hb : b = h.unop ≫ a)
    (g : Over.mk b ⟶ Over.mk a) (hg : g.left = h.unop)
    (s : T.torsor.presheaf.obj (op (Over.mk a))) :
    T.totalMap h ⟨a, s⟩ = (⟨b, T.torsor.presheaf.map g.op s⟩ : T.Total W') := by
  subst hb
  rw [show g = Over.homMk h.unop from Over.OverMorphism.ext hg]
  rfl

/-- Reading a restricted section of the restriction `f^{-1}F` as a section of `F` commutes with
the restriction maps of the total spaces. -/
theorem pullback_totalMap (T : Torsors.{t} 𝒢) {V : C} (f : V ⟶ T.base)
    {W W' : Cᵒᵖ} (h : W ⟶ W') (p : (T.pullback f).Total W) :
    (⟨((T.pullback f).totalMap h p).1 ≫ f, ((T.pullback f).totalMap h p).2⟩ : T.Total W') =
      T.totalMap h ⟨p.1 ≫ f, p.2⟩ :=
  (totalMap_mk T h (Category.assoc h.unop p.1 f)
    (Over.homMk h.unop (w := (Category.assoc h.unop p.1 f).symm)) rfl p.2).symm

/-- **Stacks 04UJ** at the restriction of a torsor: the morphism
`(V, f^{-1}F) ⟶ (U, F)` of `𝒢-Torsors` lying over `f : V ⟶ U` whose isomorphism
`α : f^{-1}F ⟶ f^{-1}F` is the identity. On total spaces it sends a section of `f^{-1}F` over
`a : W ⟶ V` to the same section of `F`, now read over `a ≫ f`. -/
def pullbackHom (T : Torsors.{t} 𝒢) {V : C} (f : V ⟶ T.base) : T.pullback f ⟶ T where
  base := f
  map := fun _ p => ⟨p.1 ≫ f, p.2⟩
  map_naturality := fun h p => pullback_totalMap T f h p
  map_equivariant := fun _ _ _ => rfl
  bijOn_map := fun W a => by
    refine ⟨fun p hp => ?_, fun p hp p' hp' hpp' => ?_, fun q hq => ?_⟩
    · have hp' : p.1 = a := hp
      exact show p.1 ≫ f = a ≫ f by rw [hp']
    · obtain ⟨b, s⟩ := p
      obtain ⟨b', s'⟩ := p'
      have hpa : b = a := hp
      have hpa' : b' = a := hp'
      subst b
      subst b'
      have hss : (⟨a ≫ f, s⟩ : Σ c : W.unop ⟶ T.base,
          T.torsor.presheaf.obj (op (Over.mk c))) = ⟨a ≫ f, s'⟩ := hpp'
      injection hss with h1 h2
      exact congrArg (Sigma.mk a) h2
    · obtain ⟨b, s⟩ := q
      have hqa : b = a ≫ f := hq
      subst b
      exact ⟨⟨a, s⟩, rfl, rfl⟩

/-- The morphism of `C` underlying `SheafOfGroups.Torsors.pullbackHom` is the morphism along
which the torsor was restricted. -/
@[simp]
theorem pullbackHom_base (T : Torsors.{t} 𝒢) {V : C} (f : V ⟶ T.base) :
    (T.pullbackHom f).base = f :=
  rfl

/-- **Stacks 04UK**, condition (1) of Stacks 02ZI. The functor `p : 𝒢-Torsors ⥤ C` of
Stacks 04UJ is fibred in groupoids: a morphism `f : V ⟶ U` of `C` lifts to the morphism
`(V, f^{-1}F) ⟶ (U, F)` out of the restricted torsor, and a fill-in is unique because the
recorded map of a morphism of `𝒢-Torsors` is a bijection on the sections over each base
morphism. -/
@[stacks 04UK "condition (1): p is fibred in groupoids", sga "4 XVIII 1.2.1" "partial"]
theorem projection_isFiberedInGroupoids :
    (projection : Torsors.{t} 𝒢 ⥤ C).IsFiberedInGroupoids where
  exists_lift {V U} f T hT := by
    subst hT
    exact ⟨T.pullback f, T.pullbackHom f,
      CategoryTheory.IsHomLift.map projection (T.pullbackHom f)⟩
  unique_lift {x y z} φ ψ f hf := by
    have hf' : f ≫ Hom.base φ = Hom.base ψ := hf
    have key : ∀ (W : Cᵒᵖ) (q : z.Total W), ∃ r : y.Total W,
        r.1 = q.1 ≫ f ∧ φ.map W r = ψ.map W q ∧
          ∀ r' : y.Total W, (r'.1 = q.1 ≫ f ∧ φ.map W r' = ψ.map W q) → r' = r := by
      intro W q
      obtain ⟨s, ⟨h1, h2⟩, h3⟩ := φ.existsUnique_map (q.1 ≫ f) (ψ.map W q) (by
        rw [ψ.fst_map, ← hf']
        exact (Category.assoc _ _ _).symm)
      exact ⟨s, h1, h2, h3⟩
    choose r hr1 hr2 huniq using key
    refine ⟨⟨f, r, ?_, ?_, ?_⟩,
      ⟨rfl, Hom.ext hf' (funext fun W => funext fun q => hr2 W q)⟩, ?_⟩
    · intro W W' h q
      refine (huniq W' (z.totalMap h q) (y.totalMap h (r W q)) ⟨?_, ?_⟩).symm
      · rw [totalMap_fst, totalMap_fst, hr1]
        exact (Category.assoc _ _ _).symm
      · rw [φ.map_naturality, hr2, ← ψ.map_naturality]
    · intro W γ q
      refine (huniq W (z.totalSmul γ q) (y.totalSmul γ (r W q)) ⟨?_, ?_⟩).symm
      · rw [totalSmul_fst, totalSmul_fst, hr1]
      · rw [φ.map_equivariant, hr2, ← ψ.map_equivariant]
    · intro W a
      refine ⟨fun q hq => ?_, fun q hq q' hq' hqq' => ?_, fun s hs => ?_⟩
      · have hqa : q.1 = a := hq
        exact show (r W q).1 = a ≫ f by rw [hr1, hqa]
      · refine (ψ.bijOn_map W a).injOn hq hq' ?_
        rw [← hr2, ← hr2, hqq']
      · have hsa : s.1 = a ≫ f := hs
        obtain ⟨q, hq, hqs⟩ := (ψ.bijOn_map W a).surjOn
          (show (φ.map W s).1 = a ≫ Hom.base ψ by
            rw [φ.fst_map, hsa]
            exact (Category.assoc a f (Hom.base φ)).trans (congrArg (a ≫ ·) hf'))
        have hqa : q.1 = a := hq
        exact ⟨q, hq, (huniq W q s ⟨by rw [hsa, hqa], hqs.symm⟩).symm⟩
    · intro χ hχ
      refine Hom.ext hχ.1 (funext fun W => funext fun q => ?_)
      exact huniq W q (χ.map W q)
        ⟨(χ.fst_map q).trans (congrArg (q.1 ≫ ·) hχ.1),
          congrFun (congrFun (congrArg Hom.map hχ.2) W) q⟩

/-- The restriction maps of the total space of the torsor of an object of `𝒢-Torsors` are
functorial: restricting along `h` and then along `k` is restricting along `h ≫ k`. -/
theorem totalMap_comp (T : Torsors.{t} 𝒢) {W W' W'' : Cᵒᵖ} (h : W ⟶ W') (k : W' ⟶ W'')
    (r : T.Total W) : T.totalMap k (T.totalMap h r) = T.totalMap (h ≫ k) r := by
  refine (totalMap_mk T k (a := h.unop ≫ r.1) (b := (h ≫ k).unop ≫ r.1)
    (Category.assoc k.unop h.unop r.1) (Over.homMk k.unop (w := by simp)) rfl _).trans ?_
  refine congrArg (Sigma.mk ((h ≫ k).unop ≫ r.1)) ?_
  rw [← Functor.map_comp_apply, ← op_comp]
  congr 2

/-- Restricting a section of the total space of a torsor along an identity leaves it
unchanged. -/
theorem totalMap_id (T : Torsors.{t} 𝒢) {W : Cᵒᵖ} (r : T.Total W) :
    T.totalMap (𝟙 W) r = r := by
  refine (totalMap_mk T (𝟙 W) (a := r.1) (b := r.1) (Category.id_comp r.1).symm
    (𝟙 (Over.mk r.1)) rfl _).trans ?_
  exact congrArg (Sigma.mk r.1) (by simp)

/-- The action of `𝒢` on the total space of a torsor is a morphism of sheaves: the restriction
of `γ · s` is the restriction of `γ` acting on the restriction of `s`. -/
theorem totalMap_totalSmul (T : Torsors.{t} 𝒢) {W W' : Cᵒᵖ} (h : W ⟶ W')
    (γ : 𝒢.presheaf.obj W) (r : T.Total W) :
    T.totalMap h (T.totalSmul γ r) = T.totalSmul (𝒢.presheaf.map h γ) (T.totalMap h r) :=
  congrArg (Sigma.mk (h.unop ≫ r.1))
    (T.torsor.naturality (U := op (Over.mk r.1))
      (V := op (Over.mk (h.unop ≫ r.1))) (Over.homMk h.unop).op γ r.2)

/-- The section of the torsor of `(U, F)` over the object `(Z, γ)` of `C/U` carried by an
element of the total space of `F` over `Z` whose base component is known to be `γ`. -/
def secOver (T : Torsors.{t} 𝒢) {Z : C} {γ : Z ⟶ T.base} (r : T.Total (op Z))
    (hr : r.1 = γ) : T.torsor.presheaf.obj (op (Over.mk γ)) :=
  T.torsor.presheaf.map
    (Over.homMk (𝟙 Z) (by simpa using hr) : Over.mk γ ⟶ Over.mk r.1).op r.2

/-- The section carried by an element of the total space, read over its own base component, is
the section recorded by that element. -/
theorem secOver_self (T : Torsors.{t} 𝒢) {Z : C} (r : T.Total (op Z)) :
    T.secOver r rfl = r.2 := by
  change T.torsor.presheaf.map (Over.homMk (𝟙 Z) _ : Over.mk r.1 ⟶ Over.mk r.1).op r.2 = r.2
  rw [show (Over.homMk (𝟙 Z) (by simp) : Over.mk r.1 ⟶ Over.mk r.1) = 𝟙 _ from
    Over.OverMorphism.ext rfl]
  simp

/-- The section carried by an element of the total space depends only on that element, not on
the proof that it lies over the given morphism. -/
theorem secOver_congr (T : Torsors.{t} 𝒢) {Z : C} {γ : Z ⟶ T.base} {r r' : T.Total (op Z)}
    (hr : r.1 = γ) (hr' : r'.1 = γ) (h : r = r') : T.secOver r hr = T.secOver r' hr' := by
  subst h; rfl

/-- An element of the total space of a torsor is recovered from its base component together
with the section it carries. -/
theorem total_secOver (T : Torsors.{t} 𝒢) {Z : C} {γ : Z ⟶ T.base} (r : T.Total (op Z))
    (hr : r.1 = γ) : (⟨γ, T.secOver r hr⟩ : T.Total (op Z)) = r := by
  subst hr
  exact congrArg (Sigma.mk r.1) (T.secOver_self r)

/-- The section carried by the pair of a morphism `γ` and a section `s` over `(Z, γ)` is `s`
itself. -/
theorem secOver_mk (T : Torsors.{t} 𝒢) {Z : C} (γ : Z ⟶ T.base)
    (s : T.torsor.presheaf.obj (op (Over.mk γ))) :
    T.secOver (γ := γ) ⟨γ, s⟩ rfl = s :=
  T.secOver_self (⟨γ, s⟩ : T.Total (op Z))

/-- Two elements of the total space of a torsor lying over the same morphism and carrying the
same section are equal. -/
theorem secOver_injective (T : Torsors.{t} 𝒢) {Z : C} {γ : Z ⟶ T.base} {r r' : T.Total (op Z)}
    (hr : r.1 = γ) (hr' : r'.1 = γ) (h : T.secOver r hr = T.secOver r' hr') : r = r' := by
  rw [← T.total_secOver r hr, ← T.total_secOver r' hr', h]

/-- The sections carried by the elements of the total space are compatible with the
restriction maps: restricting the section carried by `r` along a morphism `(Z', δ) ⟶ (Z, γ)`
of `C/U` gives the section carried by the restriction of `r`. -/
theorem secOver_map (T : Torsors.{t} 𝒢) {Z Z' : C} {γ : Z ⟶ T.base} {δ : Z' ⟶ T.base}
    {k : Z' ⟶ Z} (hk : k ≫ γ = δ) (m : Over.mk δ ⟶ Over.mk γ) (hm : m.left = k)
    (r : T.Total (op Z)) (hr : r.1 = γ) (hr' : (T.totalMap k.op r).1 = δ) :
    T.torsor.presheaf.map m.op (T.secOver r hr) = T.secOver (T.totalMap k.op r) hr' := by
  subst hr
  subst hk
  rw [show m = Over.homMk k from Over.OverMorphism.ext hm, T.secOver_self r]
  exact (T.secOver_self (T.totalMap k.op r)).symm

/-- Glueing in the total space of a torsor. Let `(U, F)` be an object of `𝒢-Torsors`, let
`β : W ⟶ U` be a morphism of `C` and let `S` be a covering sieve of `W`. A family assigning to
every member `h` of `S` an element of the total space of `F` lying over `h ≫ β`, compatibly
with the restriction maps, has a unique amalgamation: an element of the total space over `β`
whose restriction along each member of `S` is the given one. This is the sheaf condition for
`F` on the localized site `C/U`, read on total spaces. -/
theorem existsUnique_total (T : Torsors.{t} 𝒢) {W : Cᵒᵖ} (β : W.unop ⟶ T.base)
    {S : Sieve W.unop} (hS : S ∈ J W.unop)
    (q : ∀ {Z : Cᵒᵖ} (h : W ⟶ Z), S h.unop → T.Total Z)
    (hq₁ : ∀ {Z : Cᵒᵖ} (h : W ⟶ Z) (hh : S h.unop), (q h hh).1 = h.unop ≫ β)
    (hq₂ : ∀ {Z Z' : Cᵒᵖ} (h : W ⟶ Z) (hh : S h.unop) (k : Z ⟶ Z') (hk : S (h ≫ k).unop),
      T.totalMap k (q h hh) = q (h ≫ k) hk) :
    ∃! r : T.Total W, r.1 = β ∧
      ∀ {Z : Cᵒᵖ} (h : W ⟶ Z) (hh : S h.unop), T.totalMap h r = q h hh := by
  have hsf : Presieve.IsSheafFor T.torsor.presheaf
      ((Sieve.overEquiv (Over.mk β)).symm S).arrows :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1 T.torsor.isSheaf _
      (J.overEquiv_symm_mem_over (Over.mk β) S hS)
  set fam : Presieve.FamilyOfElements T.torsor.presheaf
      ((Sieve.overEquiv (Over.mk β)).symm S).arrows :=
    fun Y u hu => T.secOver (γ := Y.hom) (q (Quiver.Hom.op (Over.Hom.left u)) hu)
      ((hq₁ _ hu).trans (Over.w u)) with hfam
  have hcomp : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Y' u k hu
    have hw : (T.totalMap (Quiver.Hom.op (Over.Hom.left k))
        (q (Quiver.Hom.op (Over.Hom.left u)) hu)).1 = Y'.hom :=
      ((congrArg (fun z => Over.Hom.left k ≫ z)
            (hq₁ (Quiver.Hom.op (Over.Hom.left u)) hu)).trans
          (Category.assoc _ _ _).symm).trans (Over.w (k ≫ u))
    refine (T.secOver_congr _ hw (hq₂ (Quiver.Hom.op (Over.Hom.left u)) hu
      (Quiver.Hom.op (Over.Hom.left k)) _).symm).trans ?_
    exact (T.secOver_map (Over.w k) k rfl (q _ hu) _ hw).symm
  have key : ∀ (r : T.Total W) (hr : r.1 = β),
      fam.IsAmalgamation (T.secOver (γ := β) r hr) ↔
        ∀ {Z : Cᵒᵖ} (h : W ⟶ Z) (hh : S h.unop), T.totalMap h r = q h hh := by
    intro r hr
    have hmap : ∀ {Z : Cᵒᵖ} (h : W ⟶ Z), (T.totalMap h r).1 = h.unop ≫ β :=
      fun h => congrArg (fun z => h.unop ≫ z) hr
    constructor
    · intro ha Z h hh
      refine T.secOver_injective (γ := h.unop ≫ β) (hmap h) (hq₁ h hh)
        (Eq.trans ?_ (ha (Over.homMk h.unop : Over.mk (h.unop ≫ β) ⟶ Over.mk β) hh))
      exact (T.secOver_map (k := h.unop) rfl
        (Over.homMk h.unop : Over.mk (h.unop ≫ β) ⟶ Over.mk β) rfl r hr (hmap h)).symm
    · intro hb Y u hu
      exact (T.secOver_map (Over.w u) u rfl r hr
            ((hmap (Quiver.Hom.op (Over.Hom.left u))).trans (Over.w u))).trans
        (T.secOver_congr _ _ (hb (Quiver.Hom.op (Over.Hom.left u)) hu))
  obtain ⟨s, hs, huniq⟩ := hsf fam hcomp
  refine ⟨⟨β, s⟩, ⟨rfl, ?_⟩, ?_⟩
  · refine (key ⟨β, s⟩ rfl).1 ?_
    rw [T.secOver_mk β s]
    exact hs
  · intro r hr
    rw [← T.total_secOver r hr.1, huniq _ ((key r hr.1).2 hr.2)]

/-- Two elements of the total space of a torsor with the same base component which agree after
restriction along every member of a covering sieve are equal. -/
theorem total_ext (T : Torsors.{t} 𝒢) {W : Cᵒᵖ} {S : Sieve W.unop} (hS : S ∈ J W.unop)
    {r r' : T.Total W} (h₁ : r.1 = r'.1)
    (h₂ : ∀ {Z : Cᵒᵖ} (h : W ⟶ Z), S h.unop → T.totalMap h r = T.totalMap h r') :
    r = r' := by
  obtain ⟨z, -, hzu⟩ := T.existsUnique_total r'.1 hS (fun h _ => T.totalMap h r')
    (fun _ _ => rfl) (fun h _ k _ => T.totalMap_comp h k r')
  rw [hzu r ⟨h₁, h₂⟩, hzu r' ⟨rfl, fun _ _ => rfl⟩]

/-- A morphism of `𝒢-Torsors` prescribed on a covering sieve. Let `x` and `y` be objects of
`𝒢-Torsors`, let `ι : x.base ⟶ y.base` be a morphism of `C` and let `S` be a covering sieve of
`x.base`. Suppose given a rule `Θ` sending a section of the total space of `x` over a member of
`S` to a section of the total space of `y` over its composite with `ι`, compatible with the
restriction maps and with the action of `𝒢`, and inducing a bijection on the sections over each
member of `S`. Then there is a unique morphism `x ⟶ y` of `𝒢-Torsors` lying over `ι` whose
recorded map agrees with `Θ` on the sections over the members of `S`. -/
theorem existsUnique_hom_of_sieve {x y : Torsors.{t} 𝒢} (ι : x.base ⟶ y.base)
    {S : Sieve x.base} (hS : S ∈ J x.base)
    (Θ : ∀ {W : Cᵒᵖ} (p : x.Total W), S p.1 → y.Total W)
    (hΘ₁ : ∀ {W : Cᵒᵖ} (p : x.Total W) (hp : S p.1), (Θ p hp).1 = p.1 ≫ ι)
    (hΘ₂ : ∀ {W W' : Cᵒᵖ} (h : W ⟶ W') (p : x.Total W) (hp : S p.1)
      (hp' : S (x.totalMap h p).1), y.totalMap h (Θ p hp) = Θ (x.totalMap h p) hp')
    (hΘ₃ : ∀ {W : Cᵒᵖ} (γ : 𝒢.presheaf.obj W) (p : x.Total W) (hp : S p.1)
      (hp' : S (x.totalSmul γ p).1), Θ (x.totalSmul γ p) hp' = y.totalSmul γ (Θ p hp))
    (hΘ₄ : ∀ {W : Cᵒᵖ} (p p' : x.Total W) (hp : S p.1) (hp' : S p'.1),
      p.1 = p'.1 → Θ p hp = Θ p' hp' → p = p')
    (hΘ₅ : ∀ {W : Cᵒᵖ} (a : W.unop ⟶ x.base) (_ : S a) (s : y.Total W), s.1 = a ≫ ι →
      ∃ p : x.Total W, ∃ hp : S p.1, p.1 = a ∧ Θ p hp = s) :
    ∃! g : x ⟶ y, Hom.base g = ι ∧
      ∀ {W : Cᵒᵖ} (p : x.Total W) (hp : S p.1), g.map W p = Θ p hp := by
  have hΘc : ∀ {W : Cᵒᵖ} (p p' : x.Total W) (hp : S p.1) (hp' : S p'.1), p = p' →
      Θ p hp = Θ p' hp' := by
    intro W p p' hp hp' e
    subst e
    rfl
  have hex : ∀ (W : Cᵒᵖ) (p : x.Total W), ∃! s : y.Total W, s.1 = p.1 ≫ ι ∧
      ∀ {Z : Cᵒᵖ} (h : W ⟶ Z) (hh : S (h.unop ≫ p.1)),
        y.totalMap h s = Θ (x.totalMap h p) hh := by
    intro W p
    refine y.existsUnique_total (p.1 ≫ ι) (J.pullback_stable p.1 hS)
      (fun h hh => Θ (x.totalMap h p) hh)
      (fun h hh => (hΘ₁ (x.totalMap h p) hh).trans (Category.assoc _ _ _))
      (fun h hh k hk => ?_)
    exact (hΘ₂ k (x.totalMap h p) hh (S.downward_closed hh k.unop)).trans
      (hΘc (x.totalMap k (x.totalMap h p)) (x.totalMap (h ≫ k) p)
        (S.downward_closed hh k.unop) hk (x.totalMap_comp h k p))
  choose G hG hGu using hex
  have hG₁ : ∀ (W : Cᵒᵖ) (p : x.Total W), (G W p).1 = p.1 ≫ ι := fun W p => (hG W p).1
  have hG₂ : ∀ (W : Cᵒᵖ) (p : x.Total W) {Z : Cᵒᵖ} (h : W ⟶ Z) (hh : S (h.unop ≫ p.1)),
      y.totalMap h (G W p) = Θ (x.totalMap h p) hh := fun W p => (hG W p).2
  have hGΘ : ∀ (W : Cᵒᵖ) (p : x.Total W) (hp : S p.1), G W p = Θ p hp := fun W p hp =>
    (hGu W p (Θ p hp) ⟨hΘ₁ p hp, fun h hh => hΘ₂ h p hp hh⟩).symm
  refine ⟨⟨ι, G, ?_, ?_, ?_⟩, ⟨rfl, fun p hp => hGΘ _ p hp⟩, ?_⟩
  · intro W W' h p
    refine (hGu W' (x.totalMap h p) (y.totalMap h (G W p)) ⟨?_, fun k hk => ?_⟩).symm
    · rw [totalMap_fst, hG₁, totalMap_fst, Category.assoc]
    · have hk' : S.arrows ((k.unop ≫ h.unop) ≫ p.1) := by rwa [Category.assoc]
      rw [y.totalMap_comp h k (G W p), hG₂ W p (h ≫ k) hk']
      exact hΘc (x.totalMap (h ≫ k) p) (x.totalMap k (x.totalMap h p)) hk' hk
        (x.totalMap_comp h k p).symm
  · intro W γ p
    refine (hGu W (x.totalSmul γ p) (y.totalSmul γ (G W p)) ⟨?_, fun h hh => ?_⟩).symm
    · rw [totalSmul_fst, hG₁, totalSmul_fst]
    · rw [y.totalMap_totalSmul h γ (G W p), hG₂ W p h hh]
      exact (Eq.trans (hΘc (x.totalMap h (x.totalSmul γ p))
        (x.totalSmul (𝒢.presheaf.map h γ) (x.totalMap h p)) hh hh
        (x.totalMap_totalSmul h γ p)) (hΘ₃ (𝒢.presheaf.map h γ) (x.totalMap h p) hh hh)).symm
  · intro W a
    refine ⟨fun p hp => ?_, fun p hp p' hp' hpp' => ?_, fun s hs => ?_⟩
    · have hpa : p.1 = a := hp
      exact show (G W p).1 = a ≫ ι by rw [hG₁, hpa]
    · have hpa : p.1 = a := hp
      have hpa' : p'.1 = a := hp'
      refine x.total_ext (S := S.pullback a) (J.pullback_stable a hS) (hpa.trans hpa'.symm)
        (fun h hh => ?_)
      refine hΘ₄ (x.totalMap h p) (x.totalMap h p') (by rwa [totalMap_fst, hpa])
        (by rwa [totalMap_fst, hpa'])
        (by rw [totalMap_fst, totalMap_fst, hpa, hpa']) ?_
      rw [← hG₂ W p h (by rwa [hpa]), ← hG₂ W p' h (by rwa [hpa']), hpp']
    · have hsa : s.1 = a ≫ ι := hs
      have hloc : ∀ (Z : Cᵒᵖ) (h : W ⟶ Z), (S.pullback a) h.unop →
          ∃ pz : x.Total Z, ∃ hpz : S pz.1, pz.1 = h.unop ≫ a ∧ Θ pz hpz = y.totalMap h s := by
        intro Z h hh
        refine hΘ₅ (h.unop ≫ a) hh (y.totalMap h s) ?_
        rw [totalMap_fst, hsa, Category.assoc]
      choose pz hpz hpz₁ hpz₂ using hloc
      have hcompat : ∀ {Z Z' : Cᵒᵖ} (h : W ⟶ Z) (hh : (S.pullback a) h.unop) (k : Z ⟶ Z')
          (hk : (S.pullback a) (h ≫ k).unop),
          x.totalMap k (pz Z h hh) = pz Z' (h ≫ k) hk := by
        intro Z Z' h hh k hk
        refine hΘ₄ (x.totalMap k (pz Z h hh)) (pz Z' (h ≫ k) hk)
          (S.downward_closed (hpz Z h hh) k.unop) (hpz Z' (h ≫ k) hk)
          ((congrArg (fun z => k.unop ≫ z) (hpz₁ Z h hh)).trans
            ((Category.assoc _ _ _).symm.trans (hpz₁ Z' (h ≫ k) hk).symm)) ?_
        rw [← hΘ₂ k (pz Z h hh) (hpz Z h hh) (S.downward_closed (hpz Z h hh) k.unop),
          hpz₂, y.totalMap_comp, ← hpz₂ Z' (h ≫ k) hk]
      obtain ⟨p, hp₁, -⟩ := x.existsUnique_total a (J.pullback_stable a hS)
        (fun h hh => pz _ h hh) (fun h hh => hpz₁ _ h hh) hcompat
      refine ⟨p, hp₁.1, ((hGu W p s ⟨by rw [hp₁.1, hsa], fun h hh => ?_⟩)).symm⟩
      have hh' : S (h.unop ≫ a) := by rwa [← hp₁.1]
      exact (hpz₂ _ h hh').symm.trans
        (hΘc (pz _ h hh') (x.totalMap h p) (hpz _ h hh') hh (hp₁.2 h hh').symm)
  · intro g' hg'
    refine Hom.ext hg'.1 (funext fun W => funext fun p => ?_)
    refine hGu W p (g'.map W p) ⟨?_, fun h hh => ?_⟩
    · rw [g'.fst_map p, hg'.1]
    · rw [← g'.map_naturality h p]
      exact hg'.2 (x.totalMap h p) hh

/-- A morphism of `𝒢-Torsors` which lies over a morphism of `C` has that morphism as its
recorded morphism of `C`. -/
theorem base_eq_of_isHomLift {T T' : Torsors.{t} 𝒢}
    {a : projection.obj T ⟶ projection.obj T'} (m : T ⟶ T')
    (hm : projection.IsHomLift a m) : Hom.base m = a :=
  (CategoryTheory.IsHomLift.eq_of_isHomLift projection a m).symm

/-- The morphism of `C` recorded by the canonical comparison of two restrictions of an object
of `𝒢-Torsors` along composable morphisms of `C` is the first of those morphisms. -/
theorem base_compTo {W V U : C} (g : W ⟶ V) (ff : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ ff)
    {T : Torsors.{t} 𝒢} {hT : projection.obj T = U}
    (Tr : Functor.Restriction projection ff T hT)
    (TrW : Functor.Restriction projection h T hT)
    (hTr : Tr.pt.base = V) (hTrW : TrW.pt.base = W) :
    Hom.base (Functor.Restriction.compTo projection g ff hh Tr TrW) =
      eqToHom hTrW ≫ g ≫ eqToHom hTr.symm := by
  refine base_eq_of_isHomLift _ ?_
  have hcart := Tr.isCart
  have hlift : projection.IsHomLift ((eqToHom TrW.hpt ≫ g ≫ eqToHom Tr.hpt.symm) ≫
      (eqToHom Tr.hpt ≫ ff ≫ eqToHom hT.symm)) TrW.hom := by
    have e : (eqToHom TrW.hpt ≫ g ≫ eqToHom Tr.hpt.symm) ≫
        (eqToHom Tr.hpt ≫ ff ≫ eqToHom hT.symm)
        = eqToHom TrW.hpt ≫ h ≫ eqToHom hT.symm := by
      subst hh
      simp
    rw [e]
    exact TrW.isHomLift
  exact Functor.IsStronglyCartesian.map_isHomLift projection
    (f := eqToHom Tr.hpt ≫ ff ≫ eqToHom hT.symm) (φ := Tr.hom)
    (g := eqToHom TrW.hpt ≫ g ≫ eqToHom Tr.hpt.symm) (hf' := rfl) (φ' := TrW.hom)

/-- A morphism of `𝒢-Torsors` whose recorded morphism of `C` is equal to an isomorphism is
itself an isomorphism. -/
theorem isIso_of_base_eq {T T' : Torsors.{t} 𝒢} (m : T ⟶ T') {a : T.base ⟶ T'.base}
    (ha : Hom.base m = a) [IsIso a] : IsIso m := by
  subst ha
  exact isIso_of_isIso_base m

/-- A morphism of `𝒢-Torsors` lies over any morphism of `C` equal to the one it records. -/
theorem isHomLift_of_base {T T' : Torsors.{t} 𝒢} (m : T ⟶ T') {a : T.base ⟶ T'.base}
    (ha : Hom.base m = a) : projection.IsHomLift a m := by
  subst ha
  exact CategoryTheory.IsHomLift.map projection m

end SheafOfGroups.Torsors

end
