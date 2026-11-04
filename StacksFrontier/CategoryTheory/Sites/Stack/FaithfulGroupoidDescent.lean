module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Lifts
public import StacksFrontier.CategoryTheory.Sites.Stack.FibredOneMorphismPullback
public import StacksFrontier.CategoryTheory.Sites.Stack.Groupoid
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# Descent along a faithful 1-morphism into a stack in groupoids

Let `(𝒞, J)` be a site, let `p : 𝒮 ⥤ 𝒞` and `q : 𝒯 ⥤ 𝒞` be categories fibred in groupoids over
`𝒞` and let `F : 𝒮 ⥤ 𝒯` be a 1-morphism over `𝒞`. Assume that `𝒯` is a stack in groupoids, that
for every object `U` of `𝒞` the functor `𝒮_U ⥤ 𝒯_U` of fibre categories is faithful, and that for
every object `y` of `𝒯` over `U` the presheaf on `𝒞/U`
`(h : V ⟶ U) ↦ {(x, f) | x ∈ Ob(𝒮_V), f : F(x) ⟶ h^* y over V}/≅`
is a sheaf. Then `𝒮` is a stack in groupoids over `𝒞`.

Both descent conditions for `𝒮` are read off that sheaf. A morphism descends because, given
`α i : x|_{U i} ⟶ x'|_{U i}` agreeing on overlaps, the stack `𝒯` produces `β : F(x) ⟶ F(x')`
restricting to the `F(α i)`, and then `(x, β)` and `(x', 𝟙)` are two sections of the sheaf attached
to `y = F(x')` which agree locally, hence are isomorphic — an isomorphism being exactly a morphism
`α : x ⟶ x'` with `F(α) = β`. A descent datum descends because the object `y` of `𝒯` it descends
to turns it into a compatible family of sections of the sheaf attached to `y`.

## Main results

* `CategoryTheory.Functor.isStack_of_faithful_of_isSheaf`: Stacks 0CKJ.

## Implementation notes

"Stack in groupoids over `𝒞`" is read in the rendering of Stacks 02ZJ (3)
(`CategoryTheory.Functor.stackInGroupoids_tfae`), as a category fibred in groupoids
(`CategoryTheory.Functor.IsFiberedInGroupoids`, Stacks 003S) whose structure functor is a stack
(`CategoryTheory.Functor.IsStack`, Stacks 026F): hypothesis (1) is `hq` together with `hT`, and
the conclusion is `hp` — a hypothesis of the lemma, since `𝒮` is given fibred in groupoids —
together with `p.IsStack J`, so the conclusion carries exactly the content the lemma adds. That
rendering is used rather than the covering-family one
(`CategoryTheory.Functor.IsStackInGroupoids`, Stacks 02ZI) so that no fibre products in `𝒞` are
assumed and so that one and the same notion appears in hypothesis (1) and in the conclusion.

A 1-morphism of categories fibred in groupoids is a functor strictly over `𝒞` and nothing more
(Stacks 02ZK (2)): the condition of preserving strongly cartesian morphisms, which a 1-morphism
of fibred categories carries, is automatic here because in a category fibred in groupoids every
morphism is strongly cartesian. So `hF : F ⋙ q = p` is the whole of "`F` is a 1-morphism".

Condition (2) is stated as faithfulness of the composite `𝒮_U ⥤ 𝒮 ⥤ 𝒯` rather than of the
induced functor `𝒮_U ⥤ 𝒯_U`. The two are equivalent, because `𝒯_U ⥤ 𝒯`
(`CategoryTheory.Functor.Fiber.fiberInclusion`) is faithful and the composite factors through it;
stated this way, no proof that `F` carries `𝒮_U` into `𝒯_U` is needed inside the statement.

Condition (3) is spelled out rather than built. A morphism `F(x) ⟶ h^* y` of `𝒯_V` is the same
thing as a morphism `f : F(x) ⟶ y` of `𝒯` lying over `h`, the two being in bijection by
composition with a cartesian lift of `h` at `y`; so a pair over `h` is a morphism
`f : F.obj x ⟶ y` with `q.IsHomLift h f`, which already forces `x` to lie over `V`. The
restriction of `(x, f)` along `g : W ⟶ V` is the pair `(z, F(c) ≫ f)` for a lift `c : z ⟶ x` of
`g`, so "the class of `(x₂, f₂)` is the restriction of the class of `(x₁, f₁)` along `g`" reads
`∃ c : x₂ ⟶ x₁, p.IsHomLift g c ∧ F.map c ≫ f₁ = f₂`: no chosen pullbacks and no comparison
isomorphism enter, and for `g = 𝟙 V` that same formula is the isomorphism relation on pairs, every
morphism of a fibre of `p` being invertible. Being a sheaf is the conjunction of `hsep` (a section
is determined by its restrictions along a covering sieve, which is uniqueness of an amalgamation)
and `hglue` (a compatible family has an amalgamation). Covering sieves of an object `h : V ⟶ U` of
`𝒞/U` for `J.over U` correspond to covering sieves `R ∈ J V` (`CategoryTheory.Sieve.overEquiv`),
which is how they are quantified.

The source writes `f^* y` in condition (3) where `h^* y` is meant: `f` is the name of the morphism
of the pair, and `h : V ⟶ U` is the object of `𝒞/U` at which the presheaf is evaluated. This is a
typo of the source, recorded here rather than corrected because the objective is locked; the
statement below pulls back along `h`, the only reading under which the assignment is a presheaf.

Faithfulness. (1) No hypothesis is dead: `hp` is the standing assumption on `𝒮`, which is what
makes the conclusion the assertion "`𝒮` is a stack in groupoids"; `hq` and `hT` are the two halves
of hypothesis (1) on `𝒯`; `hF` says `F` is a 1-morphism; `hfaithful` is hypothesis (2); and `hsep`,
`hglue` are the two halves of hypothesis (3). (2) The base and the topology are the source's: one
site `(𝒞, J)`, and `p`, `q` are the structure functors of the two categories fibred in groupoids
over that same `𝒞`, with `F` strictly over `𝒞`. (3) The presheaf of condition (3) is pinned, not
asserted to exist: its sections and its restriction maps are written out in `hsep` and `hglue` in
terms of `F`, of `y` and of the lifts of the morphisms of the covering sieve, so the hypothesis is
about that presheaf and no other. (4) The hypotheses are satisfiable non-vacuously, and by an
instantiation in which `F` is not an equivalence: take `q = 𝟭 𝒞`, whose fibre categories are
trivial groupoids and which is a stack in groupoids over `𝒞`, and `F = p`. Then hypothesis (2)
says that the fibre categories of `p` are setoids, hypothesis (3) says that the presheaf
`V ↦ Ob(𝒮_V)/≅` is a sheaf, and the lemma specialises to the criterion of Stacks 0432 for a
category fibred in setoids to be a stack in setoids.

## References

* [StacksProject 0CKJ](https://stacks.math.columbia.edu/tag/0CKJ)
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

-- The chosen pullbacks of `CategoryTheory.Functor.IsPreFibered` and the inclusion of a fibre are
-- semireducible, so the endpoints of the composites below agree only up to unfolding them; this is
-- the same setting the descent files this proof reuses are elaborated in.
set_option backward.isDefEq.respectTransparency false

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒯 : Type u₃} [Category.{v₃} 𝒯]

section Helpers

section Comparison

variable {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} {F : 𝒮 ⥤ 𝒯} [p.IsFibered] [q.IsFibered]

variable {J : GrothendieckTopology 𝒞}

/-- Condition (3) of Stacks 026F for `p`, from the same condition for `q` and the gluing half of
hypothesis (3) of Stacks 0CKJ. The datum is pushed forward to `q`, where it descends to an object
`y` with cartesian morphisms `ζ` from the images of its objects; the pairs `(D f, ζ f)` are then a
compatible family for the presheaf of hypothesis (3), whose amalgamation is the object of `𝒮` the
datum descends to. -/
private theorem hasEffectiveDescent_of_glue (hF1 : IsFibredOneMorphism p q F) [F.Faithful]
    (hgpdp : p.IsFiberedInGroupoids) (hgpdq : q.IsFiberedInGroupoids)
    (hdescT : HasEffectiveDescent q J)
    (hglue : ∀ {V : 𝒞} {y : 𝒯}, q.obj y = V → ∀ {R : Sieve V}, R ∈ J V →
      ∀ (xs : ∀ ⦃W : 𝒞⦄ (g : W ⟶ V), R.arrows g → 𝒮)
        (fs : ∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R.arrows g), F.obj (xs g hg) ⟶ y),
        (∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R.arrows g), q.IsHomLift g (fs g hg)) →
        (∀ ⦃W W' : 𝒞⦄ (g : W ⟶ V) (hg : R.arrows g) (k : W' ⟶ W),
          ∃ c : xs (k ≫ g) (R.downward_closed hg k) ⟶ xs g hg,
            p.IsHomLift k c ∧ F.map c ≫ fs g hg = fs (k ≫ g) (R.downward_closed hg k)) →
        ∃ (x₀ : 𝒮) (f₀ : F.obj x₀ ⟶ y), q.IsHomLift (𝟙 V) f₀ ∧
          ∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R.arrows g), ∃ c : xs g hg ⟶ x₀,
            p.IsHomLift g c ∧ F.map c ≫ f₀ = fs g hg) :
    HasEffectiveDescent p J := by
  intro U R hR D
  obtain ⟨y₀, ζ, hζcart, hζcompat⟩ := hdescT R hR (SieveDescentDatum.mapF hF1 D)
  -- the gluing isomorphisms of `D` give, over each pair of a member of `R` and a morphism into its
  -- source, a morphism of `𝒮` over that morphism compatible with `ζ`
  have hstep : ∀ ⦃W W' : 𝒞⦄ (g : W ⟶ U) (hg : R.arrows g) (k : W' ⟶ W),
      ∃ c : (D.obj (k ≫ g) (R.downward_closed hg k)).1 ⟶ (D.obj g hg).1,
        p.IsHomLift k c ∧ F.map c ≫ ζ g hg = ζ (k ≫ g) (R.downward_closed hg k) := by
    intro W W' g hg k
    refine ⟨Fiber.fiberInclusion.map ((pullbackFiberIdIso (D.obj (k ≫ g)
        (R.downward_closed hg k))).inv ≫ (D.iso (R.downward_closed hg k) hg (𝟙 W') k
          (by simp)).hom) ≫ IsPreFibered.pullbackMap (D.obj g hg).2 k, ?_, ?_⟩
    · infer_instance
    · have haux : IsPreFibered.pullbackMap (D.obj (k ≫ g) (R.downward_closed hg k)).2 (𝟙 W') ≫
          Fiber.fiberInclusion.map (pullbackFiberIdIso (D.obj (k ≫ g)
            (R.downward_closed hg k))).inv = 𝟙 _ := by
        rw [← pullbackFiberIdIso_hom_fac, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
        rfl
      have haux2 : ∀ {T : 𝒯} (t : F.obj (pullbackFiber p (D.obj (k ≫ g)
          (R.downward_closed hg k)) (𝟙 W')).1 ⟶ T),
          F.map (IsPreFibered.pullbackMap (D.obj (k ≫ g) (R.downward_closed hg k)).2 (𝟙 W')) ≫
            F.map (Fiber.fiberInclusion.map (pullbackFiberIdIso (D.obj (k ≫ g)
              (R.downward_closed hg k))).inv) ≫ t = t := by
        intro T t
        rw [← Category.assoc, ← Functor.map_comp, haux, Functor.map_id, Category.id_comp]
      have hc := hζcompat (R.downward_closed hg k) hg (𝟙 W') k (by simp)
      simp only [SieveDescentDatum.mapF, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Functor.map_comp, Category.assoc, Fiber.fiberInclusion_map_mapOfComp_map,
        mapPbIso_inv_fac_assoc] at hc
      have hiso : q.IsStronglyCartesian (𝟙 W') (IsPreFibered.pullbackMap
          ((SieveDescentDatum.mapF hF1 D).obj (k ≫ g) (R.downward_closed hg k)).2 (𝟙 W')) :=
        inferInstance
      have : IsIso (IsPreFibered.pullbackMap
          ((SieveDescentDatum.mapF hF1 D).obj (k ≫ g) (R.downward_closed hg k)).2 (𝟙 W')) :=
        IsStronglyCartesian.isIso_of_base_isIso q (𝟙 W') _
      rw [← cancel_epi (IsPreFibered.pullbackMap
        ((SieveDescentDatum.mapF hF1 D).obj (k ≫ g) (R.downward_closed hg k)).2 (𝟙 W'))]
      simp only [Functor.map_comp, Category.assoc]
      rw [← mapPbIso_hom_fac_assoc hF1 (D.obj (k ≫ g) (R.downward_closed hg k)) (𝟙 W'),
        haux2]
      exact hc
  obtain ⟨x₀, f₀, hf₀, hcs⟩ := hglue (y := y₀.1) y₀.2 hR (fun {W} g hg ↦ (D.obj g hg).1)
    (fun {W} g hg ↦ ζ g hg) (fun {W} g hg ↦ (hζcart g hg).toIsHomLift) hstep
  have hx₀ : p.obj x₀ = U := by
    have h1 : q.obj (F.obj x₀) = U := IsHomLift.domain_eq q (𝟙 U) f₀
    rw [← hF1.comp_eq]; exact h1
  have hcs' : ∀ (W : 𝒞) (g : W ⟶ U) (hg : R.arrows g), ∃ c : (D.obj g hg).1 ⟶ x₀,
      p.IsHomLift g c ∧ F.map c ≫ f₀ = ζ g hg := fun W g hg ↦ hcs g hg
  choose cc hcc hccfac using hcs'
  -- `f₀` lies over an identity in a category fibred in groupoids, hence is an isomorphism
  have hf₀iso : IsIso f₀ := by
    have := hgpdq.isStronglyCartesian_homLift (𝟙 U) f₀
    exact IsStronglyCartesian.isIso_of_base_isIso q (𝟙 U) f₀
  refine ⟨Fiber.mk hx₀, fun {V} f hf ↦ cc V f hf, fun {V} f hf ↦ ?_, ?_⟩
  · have := hcc V f hf
    have := hgpdp.isStronglyCartesian_homLift f (cc V f hf)
    infer_instance
  · intro V W Z f hf g hg ε ε' heq
    refine F.map_injective ?_
    rw [← cancel_mono f₀]
    trace_state
    have hc := hζcompat hf hg ε ε' heq
    simp only [SieveDescentDatum.mapF, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc, Fiber.fiberInclusion_map_mapOfComp_map,
      mapPbIso_inv_fac_assoc] at hc
    simp only [Functor.map_comp, Category.assoc, hccfac]
    trace_state
    rw [← cancel_epi (Fiber.fiberInclusion.map (mapPbIso hF1 (D.obj f hf) ε).hom),
      mapPbIso_hom_fac_assoc]
    exact hc

/-- Condition (2) of Stacks 026F for `p`, from the same condition for `q` and the separatedness
half of hypothesis (3) of Stacks 0CKJ. The presheaf `Mor(x, y)` of `p` maps injectively and
naturally into the presheaf `Mor(F x, F y)` of `q`, which is a sheaf; the separatedness hypothesis
says exactly that the image of that map is closed. -/
private theorem isMorSheaf_of_locally_image (hF1 : IsFibredOneMorphism p q F) [F.Faithful]
    (hmorT : ∀ (V : 𝒞) (a b : q.Fiber V), IsMorSheaf q J V a b)
    (hsep : ∀ {V : 𝒞} {a b : 𝒮}, p.obj b = V → ∀ β : F.obj a ⟶ F.obj b,
      q.IsHomLift (𝟙 V) β → ∀ {R : Sieve V}, R ∈ J V →
      (∀ ⦃W : 𝒞⦄ (γ : W ⟶ V), R.arrows γ → ∃ (z : 𝒮) (c : z ⟶ a) (c' : z ⟶ b),
        p.IsHomLift γ c ∧ p.IsHomLift γ c' ∧ F.map c ≫ β = F.map c') →
      ∃ e : a ⟶ b, p.IsHomLift (𝟙 V) e ∧ F.map e = β)
    (U : 𝒞) (x y : p.Fiber U) : IsMorSheaf p J U x y := by
  have hffinj : ∀ {V : 𝒞} {a b : p.Fiber V} (φ ψ : a ⟶ b),
      F.map (Fiber.fiberInclusion.map φ) = F.map (Fiber.fiberInclusion.map ψ) → φ = ψ :=
    fun φ ψ h ↦ Fiber.hom_ext (F.map_injective h)
  unfold IsMorSheaf
  refine Presheaf.isSheaf_of_injective_natural
    (P := morPresheaf p x y)
    (Q := morPresheaf q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj x)
      ((Fiber.mapOfComp p q F hF1.comp_eq U).obj y))
    (fun w (m : pullbackFiber p x (Opposite.unop w).hom ⟶
        pullbackFiber p y (Opposite.unop w).hom) ↦
      (mapPbIso hF1 x (Opposite.unop w).hom).hom ≫
        (Fiber.mapOfComp p q F hF1.comp_eq (Opposite.unop w).left).map m ≫
        (mapPbIso hF1 y (Opposite.unop w).hom).inv)
    ?_ ?_ (hmorT U _ _) ?_
  · rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩ m
    dsimp only [morPresheaf_map_apply, Quiver.Hom.unop_op']
    refine morRestrict_uniq q _ _ h _ _ ?_
    simp only [Functor.map_comp, Category.assoc,
      mapPbIso_inv_fac,
      Fiber.fiberInclusion_map_mapOfComp_map]
    rw [← Functor.map_comp, morRestrict_fac, Functor.map_comp, Functor.map_comp,
      ← pullbackFiberMap_mapPbIso_hom_assoc hF1 x h]
  · rintro ⟨g⟩ m n hmn
    have h2 : (Fiber.mapOfComp p q F hF1.comp_eq g.left).map m =
        (Fiber.mapOfComp p q F hF1.comp_eq g.left).map n := by
      rw [← cancel_epi (mapPbIso hF1 x g.hom).hom,
        ← cancel_mono (mapPbIso hF1 y g.hom).inv]
      simpa only [Category.assoc] using hmn
    exact hffinj m n (congrArg Fiber.fiberInclusion.map h2)
  · intro g S hS β hβloc
    have hR : Sieve.overEquiv g S ∈ J g.left := (J.mem_over_iff S).1 hS
    have hloc : ∀ ⦃W : 𝒞⦄ (γ : W ⟶ g.left), (Sieve.overEquiv g S).arrows γ →
        ∃ (z : 𝒮) (c : z ⟶ (pullbackFiber p x g.hom).1)
          (c' : z ⟶ (pullbackFiber p y g.hom).1),
          p.IsHomLift γ c ∧ p.IsHomLift γ c' ∧
          F.map c ≫ Fiber.fiberInclusion.map ((mapPbIso hF1 x g.hom).inv ≫ β ≫
            (mapPbIso hF1 y g.hom).hom) = F.map c' := by
      intro W γ hγ
      let k : (Over.mk (γ ≫ g.hom) : Over U) ⟶ g := Over.homMk γ
      obtain ⟨m, hm⟩ := hβloc k ((Sieve.overEquiv_iff S γ).1 hγ)
      have hkx : p.IsHomLift γ (pullbackFiberMap p x k) :=
        pullbackFiberMap_isHomLift p x k
      have hky : p.IsHomLift γ (pullbackFiberMap p y k) :=
        pullbackFiberMap_isHomLift p y k
      have hmlift : p.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map m) := m.2
      have hkxy : p.IsHomLift γ (Fiber.fiberInclusion.map m ≫
          pullbackFiberMap p y k) := inferInstance
      refine ⟨_, pullbackFiberMap p x k,
        Fiber.fiberInclusion.map m ≫ pullbackFiberMap p y k,
        hkx, hkxy, ?_⟩
      have hscart : q.IsStronglyCartesian g.hom
          (F.map (IsPreFibered.pullbackMap y.2 g.hom)) :=
        hF1.map_isStronglyCartesian g.hom _ inferInstance
      have hl1 : q.IsHomLift γ (F.map (pullbackFiberMap p x k)) :=
        hF1.map_isHomLift γ _
      have hl2 : q.IsHomLift γ (F.map (Fiber.fiberInclusion.map m ≫
          pullbackFiberMap p y k)) := hF1.map_isHomLift γ _
      refine IsStronglyCartesian.ext q g.hom (F.map (IsPreFibered.pullbackMap y.2 g.hom)) γ ?_
      have hm' : (mapPbIso hF1 x (Over.mk (γ ≫ g.hom) : Over U).hom).hom ≫
          (Fiber.mapOfComp p q F hF1.comp_eq W).map m ≫
          (mapPbIso hF1 y (Over.mk (γ ≫ g.hom) : Over U).hom).inv =
          morRestrict q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj x)
            ((Fiber.mapOfComp p q F hF1.comp_eq U).obj y) k β := hm
      have hres := morRestrict_fac q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj x)
        ((Fiber.mapOfComp p q F hF1.comp_eq U).obj y) k β
      rw [← hm'] at hres
      have hcancel : Fiber.fiberInclusion.map (mapPbIso hF1 x g.hom).hom ≫
          Fiber.fiberInclusion.map (mapPbIso hF1 x g.hom).inv = 𝟙 _ := by
        rw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
      simp only [Functor.map_comp, Category.assoc, mapPbIso_hom_fac]
      rw [← Functor.map_comp F, pullbackFiberMap_fac]
      rw [← cancel_epi (Fiber.fiberInclusion.map
        (mapPbIso hF1 x (Over.mk (γ ≫ g.hom) : Over U).hom).hom)]
      rw [← Category.assoc, ← pullbackFiberMap_mapPbIso_hom hF1 x k]
      simp only [Category.assoc, ← Functor.map_comp]
      rw [← Category.assoc (Fiber.fiberInclusion.map (mapPbIso hF1 x g.hom).hom), hcancel,
        Category.id_comp, ← hres]
      simp only [Functor.map_comp, Category.assoc, mapPbIso_inv_fac]
      rfl
    obtain ⟨e, hehl, he⟩ := hsep (pullbackFiber p y g.hom).2 _ inferInstance hR hloc
    refine ⟨⟨e, hehl⟩, ?_⟩
    have hmap : (Fiber.mapOfComp p q F hF1.comp_eq g.left).map
        (⟨e, hehl⟩ : pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom) =
        (mapPbIso hF1 x g.hom).inv ≫ β ≫ (mapPbIso hF1 y g.hom).hom :=
      Fiber.hom_ext he
    dsimp only
    rw [hmap]
    simp
end Comparison

end Helpers

/-- **Descent along a faithful 1-morphism into a stack in groupoids.** Let `(𝒞, J)` be a site and
let `F : 𝒮 ⥤ 𝒯` be a 1-morphism of categories fibred in groupoids over `𝒞`, that is a functor
with `F ⋙ q = p`. Assume that (1) `𝒯` is a stack in groupoids over `𝒞`, (2) for every object `U`
of `𝒞` the functor `𝒮_U ⥤ 𝒯_U` of fibre categories is faithful, and (3) for every object `y` of
`𝒯` over `U` the presheaf on `𝒞/U` sending `h : V ⟶ U` to the isomorphism classes of pairs
`(x, f)` with `x` an object of `𝒮_V` and `f : F(x) ⟶ h^* y` a morphism of `𝒯_V` is a sheaf. Then
`𝒮` is a stack in groupoids over `𝒞`.

Condition (3) is the two hypotheses `hsep` and `hglue`, in which a pair over `h` is a morphism
`f : F.obj x ⟶ y` lying over `h`, and the class of `(x₂, f₂)` is the restriction of the class of
`(x₁, f₁)` along `g : W ⟶ V` when `F.map c ≫ f₁ = f₂` for some lift `c : x₂ ⟶ x₁` of `g`. -/
@[stacks 0CKJ]
public theorem isStack_of_faithful_of_isSheaf {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} {F : 𝒮 ⥤ 𝒯}
    {J : GrothendieckTopology 𝒞} (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hF : F ⋙ q = p) (hT : q.IsStack J)
    (hfaithful : ∀ U : 𝒞, (Fiber.fiberInclusion (p := p) (S := U) ⋙ F).Faithful)
    (hsep : ∀ (y : 𝒯) ⦃V : 𝒞⦄ (h : V ⟶ q.obj y) (R : Sieve V), R ∈ J V →
      ∀ ⦃x x' : 𝒮⦄ (f : F.obj x ⟶ y) (f' : F.obj x' ⟶ y),
        q.IsHomLift h f → q.IsHomLift h f' →
        (∀ ⦃W : 𝒞⦄ (g : W ⟶ V), R g → ∃ (z : 𝒮) (c : z ⟶ x) (c' : z ⟶ x'),
          p.IsHomLift g c ∧ p.IsHomLift g c' ∧ F.map c ≫ f = F.map c' ≫ f') →
        ∃ e : x ⟶ x', p.IsHomLift (𝟙 V) e ∧ F.map e ≫ f' = f)
    (hglue : ∀ (y : 𝒯) ⦃V : 𝒞⦄ (h : V ⟶ q.obj y) (R : Sieve V), R ∈ J V →
      ∀ (x : ∀ ⦃W : 𝒞⦄ (g : W ⟶ V), R g → 𝒮)
        (f : ∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R g), F.obj (x g hg) ⟶ y),
        (∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R g), q.IsHomLift (g ≫ h) (f g hg)) →
        (∀ ⦃W W' : 𝒞⦄ (g : W ⟶ V) (hg : R g) (k : W' ⟶ W),
          ∃ c : x (k ≫ g) (R.downward_closed hg k) ⟶ x g hg,
            p.IsHomLift k c ∧ F.map c ≫ f g hg = f (k ≫ g) (R.downward_closed hg k)) →
        ∃ (x₀ : 𝒮) (f₀ : F.obj x₀ ⟶ y), q.IsHomLift h f₀ ∧
          ∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R g), ∃ c : x g hg ⟶ x₀,
            p.IsHomLift g c ∧ F.map c ≫ f₀ = f g hg) :
    p.IsStack J := by
  subst hF
  have hqfib : q.IsFibered := hq.isFibered
  have hpfib : (F ⋙ q).IsFibered := hp.isFibered
  -- `F` is a 1-morphism of fibred categories: preservation of strongly cartesian morphisms is
  -- automatic because `q` is fibred in groupoids (Stacks 02ZK (2)).
  have hF1 : IsFibredOneMorphism (F ⋙ q) q F :=
    IsFibredOneMorphism.of_isFiberedInGroupoids hq rfl
  -- `F` is faithful, by Stacks 003Z (1) applied to the fibrewise hypothesis (2).
  have hFfaith : F.Faithful := by
    rw [IsFiberedInGroupoids.faithful_iff_forall_fiber (F ⋙ q) q hp hq F rfl]
    intro U
    have := hfaithful U
    exact Faithful.of_comp_eq (Fiber.mapOfComp_comp_fiberInclusion (F ⋙ q) q F rfl U)
  -- hence a morphism of a fibre of `p` is determined by its image under `F`
  -- Hypothesis (3), separatedness half, in raw form: a morphism `β : F a ⟶ F b` over an identity
  -- that is locally in the image of `F` is in the image of `F`.
  have hsep' : ∀ {V : 𝒞} {a b : 𝒮}, (F ⋙ q).obj b = V → ∀ (β : F.obj a ⟶ F.obj b),
      q.IsHomLift (𝟙 V) β → ∀ {R : Sieve V}, R ∈ J V →
      (∀ ⦃W : 𝒞⦄ (γ : W ⟶ V), R.arrows γ → ∃ (z : 𝒮) (c : z ⟶ a) (c' : z ⟶ b),
        (F ⋙ q).IsHomLift γ c ∧ (F ⋙ q).IsHomLift γ c' ∧ F.map c ≫ β = F.map c') →
      ∃ e : a ⟶ b, (F ⋙ q).IsHomLift (𝟙 V) e ∧ F.map e = β := by
    intro V a b hb β hβ R hR hloc
    subst hb
    obtain ⟨e, he, hfac⟩ := hsep (F.obj b) (𝟙 _) R hR β (𝟙 (F.obj b)) hβ (IsHomLift.id rfl)
      (fun {_W} γ hγ ↦ by
        obtain ⟨z, c, c', h1, h2, h3⟩ := hloc γ hγ
        exact ⟨z, c, c', h1, h2, by rw [h3, Category.comp_id]⟩)
    exact ⟨e, he, by simpa using hfac⟩
  -- Hypothesis (3), gluing half, in raw form: a compatible family of pairs over a covering sieve
  -- has an amalgamation.
  have hglue' : ∀ {V : 𝒞} {y : 𝒯}, q.obj y = V → ∀ {R : Sieve V}, R ∈ J V →
      ∀ (xs : ∀ ⦃W : 𝒞⦄ (g : W ⟶ V), R.arrows g → 𝒮)
        (fs : ∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R.arrows g), F.obj (xs g hg) ⟶ y),
        (∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R.arrows g), q.IsHomLift g (fs g hg)) →
        (∀ ⦃W W' : 𝒞⦄ (g : W ⟶ V) (hg : R.arrows g) (k : W' ⟶ W),
          ∃ c : xs (k ≫ g) (R.downward_closed hg k) ⟶ xs g hg,
            (F ⋙ q).IsHomLift k c ∧ F.map c ≫ fs g hg = fs (k ≫ g) (R.downward_closed hg k)) →
        ∃ (x₀ : 𝒮) (f₀ : F.obj x₀ ⟶ y), q.IsHomLift (𝟙 V) f₀ ∧
          ∀ ⦃W : 𝒞⦄ (g : W ⟶ V) (hg : R.arrows g), ∃ c : xs g hg ⟶ x₀,
            (F ⋙ q).IsHomLift g c ∧ F.map c ≫ f₀ = fs g hg := by
    intro V y hy R hR xs fs hfs hcompat
    subst hy
    exact hglue y (𝟙 _) R hR xs fs (fun {W} g hg ↦ by simpa using hfs g hg) hcompat
  refine ⟨hp.isFibered, ?_, ?_⟩
  · exact fun U x y ↦ isMorSheaf_of_locally_image hF1 hT.isMorSheaf hsep' U x y
  · exact hasEffectiveDescent_of_glue hF1 hp hq hT.hasEffectiveDescent hglue'

end CategoryTheory.Functor

end
