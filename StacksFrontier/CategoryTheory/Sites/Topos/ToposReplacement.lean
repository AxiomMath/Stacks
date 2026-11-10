module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismsOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Topos.RepresentedMorphismOfSites
import StacksCore.Tactic.StacksAttribute

/-!
# Replacing a morphism of topoi by a morphism of sites on both sides

Let `(C, J)` and `(D, K)` be sites and let `f : Sh(C) → Sh(D)` be a morphism of topoi. Stacks
03A2 replaces the *source* site by a site `(C', J')` so that `f` becomes the composition of an
equivalence `g : Sh(C) → Sh(C')` with a morphism of topoi coming from a morphism of sites. Stacks
03CJ observes two further things:

1. the functor `u : D ⥤ C'` produced by Stacks 03A2 also transforms the final object of `D` into
   the final object of `C'`, so that it satisfies *all* the hypotheses of Stacks 00X6 as soon as
   `D` has a final object and fibre products; and
2. applying Stacks 03CI to `D` first and Stacks 03A2 to the resulting morphism of topoi
   `Sh(C) → Sh(D')` replaces the morphism on *both* sides, with `D'` a site having all finite
   limits.

Part (1) is recorded where it belongs, in the conclusion of
`MorphismOfTopoi.exists_isDenseSubsite_isMorphismOfSites_pushforward_iso` (Stacks 03A2), since it
is an assertion about the construction carried out in that proof. This file carries part (2), with
a second application of Stacks 03CI — to the site Stacks 03A2 produces — giving the source site
the same properties as the target site.

## Main definitions

* `CategoryTheory.Functor.IsDenseSubsite.morphismOfTopoi`: the morphism of topoi
  `Sh(C) → Sh(D)` attached to a functor exhibiting `(C, J)` as a dense subsite of `(D, K)`, i.e.
  to a special cocontinuous functor (Stacks 03CG). Its pushforward is
  `Functor.sheafPushforwardCocontinuous` and its inverse image is restriction along the functor,
  which is an equivalence; so this is an *equivalence* of topoi (Stacks 03A0).
* `CategoryTheory.Functor.sheafPushforwardCocontinuousCompOfContinuous`: the pushforward of sheaves
  along a composite of continuous and cocontinuous functors is the composite of the pushforwards.

## Main results

* `CategoryTheory.Functor.isDenseSubsite_comp`: special cocontinuous functors compose, i.e. a
  dense subsite of a dense subsite is a dense subsite.

* `MorphismOfTopoi.exists_twoSided_isDenseSubsite_representablyFlat` (Stacks 03CJ): every
  morphism of topoi `f : Sh(C) → Sh(D)` between sites fits in a commutative square
  `e ∘ f = h ∘ g` in which `g` and `e` are the equivalences induced by special cocontinuous
  functors `C ⥤ C'` and `D ⥤ D'`, the topologies of `C'` and `D'` are subcanonical, both `C'` and
  `D'` have all finite limits, prescribed families of sheaves on `C` and on `D` become
  representable on `C'` and on `D'`, and `h` comes from a continuous functor `u : D' ⥤ C'` which
  preserves all finite limits — hence is representably flat and defines a morphism of sites by
  Stacks 00X6.

## Implementation notes

**What of Stacks 03CJ is carried.** The source's remark lists four conclusions, and all four are
carried.

* Conclusion (1) — `e` and `g` are equivalences given by special cocontinuous functors
  `C ⥤ C'`, `D ⥤ D'` — is carried, as the two `Functor.IsDenseSubsite` fields; that these induce
  equivalences of topoi is Stacks 03A0, available as
  `CategoryTheory.Functor.IsDenseSubsite.morphismOfTopoi` below.
* Conclusion (2) — `C'` and `D'` have all finite limits, with subcanonical topologies — is
  carried for both sites. The site produced by the formalization of Stacks 03A2 is the full
  subcategory of `Sh(C)` on the objects `h_U^#` and `f⁻¹h_V^#`, which is *not* closed under fibre
  products, whereas the source closes it up; instead of closing it up by hand, Stacks 03CI is
  applied a second time, to that site, which both closes it up and makes the prescribed sheaves
  representable. The replacement of the source site is then the composite
  `C ⥤ C₁ ⥤ C'` of two special cocontinuous functors (`Functor.isDenseSubsite_comp`), and the
  functor `u` is the composite `D' ⥤ C₁ ⥤ C'`.
* Conclusion (3) — `h` comes from a functor `u : D' ⥤ C'` to which Stacks 00X6 applies — is
  carried in the strongest available form: `PreservesFiniteLimits u` together with
  `HasFiniteLimits D'`, plus the two consequences `RepresentablyFlat u` (Stacks 00X3) and
  `u.IsMorphismOfSites K' J'` (Stacks 00X6) spelled out. Left exactness survives the composition
  with `C₁ ⥤ C'` because the functor Stacks 03CI produces is `U ↦ h_U^#` read in a full
  subcategory of the topos, which preserves every finite limit that exists in its source.
* Conclusion (4) — a prescribed set of sheaves on `C` (resp. `D`) may be assumed representable on
  `C'` (resp. `D'`) — is carried on both sides: the `D` half is conclusion (5) of Stacks 03CI for
  the first application, and the `C` half is conclusion (5) of Stacks 03CI for the second, read
  through the identification of the pushforward along `C ⥤ C₁ ⥤ C'` with the composite of the two
  pushforwards (`Functor.sheafPushforwardCocontinuousCompOfContinuous`).

The universes are those of a Stacks site: `C` and `D` are `SmallCategory`s on `Type u`, so that
the topos is `Sheaf _ (Type u)`. This is forced, not chosen: Stacks 03CI applied to a site
`(D, K)` with `D : Type u₂` and `Category.{v₂} D` produces `D' : Type max u₂ v₂` carrying
`Category.{max u₂ v₂} D'`, and Stacks 03A2 requires its two sites to have *the same* object and
morphism universes, so the only way to feed the output of the first into the second is
`u₂ = v₂ = max u₂ v₂`.

## References

* [Stacks 03CJ](https://stacks.math.columbia.edu/tag/03CJ)
  (`sites-remark-improve-morphism-topoi`)
* [Stacks 03A2](https://stacks.math.columbia.edu/tag/03A2),
  [Stacks 03CI](https://stacks.math.columbia.edu/tag/03CI),
  [Stacks 00X6](https://stacks.math.columbia.edu/tag/00X6),
  [Stacks 00X3](https://stacks.math.columbia.edu/tag/00X3)
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.Functor

/-- Special cocontinuous functors compose: if `(C, J)` is a dense subsite of `(D, K)` and
`(D, K)` is a dense subsite of `(E, L)`, then `(C, J)` is a dense subsite of `(E, L)`.

All four conditions of `Functor.IsDenseSubsite` transfer. The sieve condition is immediate from
`Sieve.functorPushforward_comp`; cover density of the composite is the `L`-covering of an object
of `E` by objects of `D`, refined through the `L`-covering of each of those by objects of `C`;
and local fullness and local faithfulness of the composite come from those of `G` lifted along
`F` (which is continuous, hence lifts covers) and then refined by those of `F`. -/
theorem isDenseSubsite_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (F : C ⥤ D) (G : D ⥤ E) [F.IsDenseSubsite J K]
    [G.IsDenseSubsite K L] : (F ⋙ G).IsDenseSubsite J L := by
  have push {X : C} {S : Sieve X} : S.functorPushforward (F ⋙ G) ∈ L _ ↔ S ∈ J _ := by
    rw [Sieve.functorPushforward_comp]
    change (S.functorPushforward F).functorPushforward G ∈ L (G.obj (F.obj X)) ↔ _
    rw [G.functorPushforward_mem_iff K L, F.functorPushforward_mem_iff J K]
  refine { isCoverDense' := ⟨fun X => ?_⟩
           isLocallyFull' := ⟨fun {_ _} f => push.mpr ?_⟩
           isLocallyFaithful' := ⟨fun f g h => push.mpr ?_⟩
           functorPushforward_mem_iff := push }
  · apply L.transitive (Functor.IsDenseSubsite.isCoverDense K L G |>.is_cover X)
    rintro Y _ ⟨⟨Z, a, b, rfl⟩⟩
    rw [Sieve.pullback_comp]
    apply L.pullback_stable
    have hc := (G.functorPushforward_mem_iff K L).mpr
      (Functor.IsDenseSubsite.isCoverDense J K F |>.is_cover Z)
    apply L.superset_covering _ hc
    rintro W _ ⟨V, k, l, ⟨⟨T, m, n, rfl⟩⟩, rfl⟩
    exact ⟨⟨T, l ≫ G.map m, G.map n ≫ b, by simp⟩⟩
  · have hS := Functor.IsDenseSubsite.imageSieve_mem K L G f
    apply J.transitive (F.cover_lift J K hS)
    intro W i hi
    obtain ⟨l, hl⟩ := hi
    apply J.superset_covering _ (Functor.IsDenseSubsite.imageSieve_mem J K F l)
    intro Z j hj
    obtain ⟨m, hm⟩ := hj
    exact ⟨m, by dsimp; rw [hm, G.map_comp, hl]; simp⟩
  · have hS := Functor.IsDenseSubsite.equalizer_mem K L G (F.map f) (F.map g) h
    apply J.transitive (F.cover_lift J K hS)
    intro W i hi
    have he : F.map (i ≫ f) = F.map (i ≫ g) := by simpa using hi
    apply J.superset_covering _ (Functor.IsDenseSubsite.equalizer_mem J K F _ _ he)
    intro Z j hj
    simpa [Sieve.equalizer, Category.assoc] using hj

/-- The pushforward of sheaves along a composite of functors that are both continuous and
cocontinuous is the composite of the pushforwards: both are right adjoint to the composite of the
restriction functors, which is the restriction along the composite
(`Functor.sheafPushforwardContinuousComp`). -/
@[sga "4 III 4.4" "special case"]
noncomputable def sheafPushforwardCocontinuousCompOfContinuous {C : Type u₁} [SmallCategory C]
    {D : Type u₁} [SmallCategory D] {E : Type u₁} [SmallCategory E] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E) (F : C ⥤ D) (G : D ⥤ E)
    [F.IsContinuous J K] [F.IsCocontinuous J K] [G.IsContinuous K L] [G.IsCocontinuous K L]
    [(F ⋙ G).IsContinuous J L] [(F ⋙ G).IsCocontinuous J L] :
    (F ⋙ G).sheafPushforwardCocontinuous (Type u₁) J L ≅
      F.sheafPushforwardCocontinuous (Type u₁) J K ⋙
        G.sheafPushforwardCocontinuous (Type u₁) K L :=
  Adjunction.rightAdjointUniq ((F ⋙ G).sheafAdjunctionCocontinuous (Type u₁) J L)
    (((G.sheafAdjunctionCocontinuous (Type u₁) K L).comp
      (F.sheafAdjunctionCocontinuous (Type u₁) J K)).ofNatIsoLeft
        (F.sheafPushforwardContinuousComp G (Type u₁) J K L))

end CategoryTheory.Functor

namespace CategoryTheory.Functor.IsDenseSubsite

/-- The morphism of topoi `Sh(C) → Sh(D)` attached to a functor `w : C ⥤ D` exhibiting `(C, J)`
as a dense subsite of `(D, K)`, i.e. to a special cocontinuous functor in the sense of Stacks
03CG.

Its pushforward is `w.sheafPushforwardCocontinuous`, the right Kan extension along `w.op`, and
its inverse image is `w.sheafPushforwardContinuous`, plain restriction along `w`. The latter is
an equivalence of categories (Mathlib's `IsDenseSubsite.sheafEquiv`, the content of Stacks 03A0),
so it is in particular left exact; thus this is an *equivalence* of topoi. -/
@[sga "4 IV 4.7" "special case"]
noncomputable def morphismOfTopoi {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
    [w.IsDenseSubsite J K] : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)) where
  pushforward := w.sheafPushforwardCocontinuous (Type u) J K
  inverseImage := w.sheafPushforwardContinuous (Type u) J K
  adj := w.sheafAdjunctionCocontinuous (Type u) J K
  preservesFiniteLimits := inferInstance

/-- The pushforward of `morphismOfTopoi J K w` is `w.sheafPushforwardCocontinuous`. -/
@[simp]
theorem morphismOfTopoi_pushforward {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
    [w.IsDenseSubsite J K] :
    (morphismOfTopoi J K w).pushforward = w.sheafPushforwardCocontinuous (Type u) J K :=
  rfl

/-- The inverse image of `morphismOfTopoi J K w` is `w.sheafPushforwardContinuous`, restriction
along `w`. -/
@[simp]
theorem morphismOfTopoi_inverseImage {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
    [w.IsDenseSubsite J K] :
    (morphismOfTopoi J K w).inverseImage = w.sheafPushforwardContinuous (Type u) J K :=
  rfl

/-- The morphism of topoi attached to a special cocontinuous functor is an equivalence of topoi:
its direct image is an equivalence of categories. Its inverse image is restriction along the
functor, an equivalence by Stacks 03A0, and the direct image is right adjoint to that. -/
theorem morphismOfTopoi_pushforward_isEquivalence {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
    [w.IsDenseSubsite J K] :
    (morphismOfTopoi J K w).pushforward.IsEquivalence := by
  change (w.sheafPushforwardCocontinuous (Type u) J K).IsEquivalence
  exact Adjunction.isEquivalence_right_of_isEquivalence_left
    (w.sheafAdjunctionCocontinuous (Type u) J K)

end CategoryTheory.Functor.IsDenseSubsite

namespace MorphismOfTopoi

/-- If the counit of `L ⊣ R` is an isomorphism, then `R ⋙ L ⋙ M` is isomorphic to `M`. -/
private noncomputable def counitCancel {A : Type*} [Category A] {B : Type*} [Category B]
    {E : Type*} [Category E] {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [IsIso adj.counit]
    (M : B ⥤ E) : R ⋙ L ⋙ M ≅ M :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (asIso adj.counit) M ≪≫
    Functor.leftUnitor _

/-- Let `(C, J)` and `(D, K)` be sites and let `f : Sh(C) → Sh(D)` be a morphism of topoi. Then
there are sites `(C', J')` and `(D', K')`, special cocontinuous functors `v : C ⥤ C'` and
`w : D ⥤ D'`, and a functor `u : D' ⥤ C'` such that

1. `v` and `w` exhibit `(C, J)` and `(D, K)` as dense subsites, so the morphisms of topoi
   `g : Sh(C) → Sh(C')` and `e : Sh(D) → Sh(D')` they induce are equivalences (Stacks 03A0);
2. `J'` and `K'` are subcanonical and `C'` and `D'` have all finite limits;
3. `u` is continuous, preserves all finite limits, is representably flat and defines a morphism
   of sites `C' → D'` — in other words Stacks 00X6 applies to `u`;
4. each `g_*(F i)` is a representable sheaf on `C'` and each `e_*(G j)` is a representable sheaf
   on `D'`, for prescribed families of sheaves `F` on `C` and `G` on `D`; and
5. the square commutes: `f_* ⋙ e_*` is isomorphic to `g_* ⋙ h_*`, where `h : Sh(C') → Sh(D')`
   is the morphism of topoi attached to the morphism of sites `u`.

Conclusions (1)-(4) are the source's conclusions (1)-(4) and (5) is the commutativity of the
square the source's remark is about. -/
@[stacks 03CJ "Any morphism of topoi fits into a commutative square with two equivalences given
  by special cocontinuous functors and a morphism of topoi coming from a functor `u : D' ⥤ C'`
  to which Stacks 00X6 applies, with both `C'` and `D'` having all finite limits and subcanonical
  topologies, and with prescribed families of sheaves on `C` and on `D` becoming representable on
  `C'` and on `D'`."]
theorem exists_twoSided_isDenseSubsite_representablyFlat {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))) {ι : Type u}
    (F : ι → Sheaf J (Type u)) {κ : Type u} (G : κ → Sheaf K (Type u)) :
    ∃ (C' : Type u) (_ : SmallCategory C') (J' : GrothendieckTopology C') (D' : Type u)
      (_ : SmallCategory D') (K' : GrothendieckTopology D') (v : C ⥤ C') (w : D ⥤ D')
      (u : D' ⥤ C') (_ : v.IsDenseSubsite J J') (_ : w.IsDenseSubsite K K')
      (_ : HasFiniteLimits C') (_ : HasFiniteLimits D') (_ : J'.Subcanonical)
      (_ : K'.Subcanonical) (_ : u.IsContinuous K' J') (_ : PreservesFiniteLimits u)
      (_ : RepresentablyFlat u) (_ : u.IsMorphismOfSites K' J'),
      (∀ i, ((v.sheafPushforwardCocontinuous (Type u) J J').obj (F i)).obj.IsRepresentable) ∧
      (∀ j, ((w.sheafPushforwardCocontinuous (Type u) K K').obj (G j)).obj.IsRepresentable) ∧
      Nonempty
        (f.pushforward ⋙ w.sheafPushforwardCocontinuous (Type u) K K' ≅
          v.sheafPushforwardCocontinuous (Type u) J J' ⋙
            u.sheafPushforwardContinuous (Type u) K' J') := by
  -- Stacks 03CI applied to `(D, K)` and the family `G`: a site `(D', K')` with all finite limits
  -- and a subcanonical topology, a special cocontinuous `w : D ⥤ D'`, and each `w_*(G j)`
  -- representable.
  obtain ⟨D', instD', K', w, instw, hsubK, hflD, -, -, hrepG⟩ :=
    K.exists_isDenseSubsite_subcanonical_hasFiniteLimits_representable G
  -- Stacks 03A2 applied to the composition `Sh(C) → Sh(D) → Sh(D')`.
  obtain ⟨C₁, instC₁, J₁, v₁, u₁, instv₁, hmos, hcospan, hpempty, ⟨iso⟩⟩ :=
    (MorphismOfTopoi.comp (Functor.IsDenseSubsite.morphismOfTopoi K K' w) f)
      |>.exists_isDenseSubsite_isMorphismOfSites_pushforward_iso
  -- Stacks 03CI applied again, now to `(C₁, J₁)` and the family of direct images of `F`: this is
  -- what makes the *source* site finitely complete, subcanonical, and the `F i` representable.
  obtain ⟨C', instC', J', t, instt, hsubJ, hflC, hpflt, -, hrepF⟩ :=
    J₁.exists_isDenseSubsite_subcanonical_hasFiniteLimits_representable
      (fun i => (v₁.sheafPushforwardCocontinuous (Type u) J J₁).obj (F i))
  have hcompDense : (v₁ ⋙ t).IsDenseSubsite J J' := Functor.isDenseSubsite_comp J J₁ J' v₁ t
  have hpflu₁ : PreservesFiniteLimits u₁ :=
    have := hcospan
    have := hpempty
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks u₁
  have hcontu : (u₁ ⋙ t).IsContinuous K' J' := Functor.isContinuous_comp u₁ t K' J₁ J'
  have hpflu : PreservesFiniteLimits (u₁ ⋙ t) := comp_preservesFiniteLimits u₁ t
  -- The pushforward of the composite special cocontinuous functor is the composite of the
  -- pushforwards, and the two pushforwards of `t` cancel, so the square still commutes.
  let compCocont := Functor.sheafPushforwardCocontinuousCompOfContinuous J J₁ J' v₁ t
  let compCont := Functor.sheafPushforwardContinuousComp u₁ t (Type u) K' J₁ J'
  let adjT := t.sheafAdjunctionCocontinuous (Type u) J₁ J'
  have : IsIso adjT.counit := NatIso.isIso_of_isIso_app _
  have square :
      (v₁ ⋙ t).sheafPushforwardCocontinuous (Type u) J J' ⋙
          (u₁ ⋙ t).sheafPushforwardContinuous (Type u) K' J' ≅
        v₁.sheafPushforwardCocontinuous (Type u) J J₁ ⋙
          u₁.sheafPushforwardContinuous (Type u) K' J₁ :=
    Functor.isoWhiskerRight compCocont ((u₁ ⋙ t).sheafPushforwardContinuous (Type u) K' J') ≪≫
      Functor.isoWhiskerLeft
        (v₁.sheafPushforwardCocontinuous (Type u) J J₁ ⋙
          t.sheafPushforwardCocontinuous (Type u) J₁ J') compCont.symm ≪≫
      Functor.isoWhiskerLeft _
        (counitCancel adjT (u₁.sheafPushforwardContinuous (Type u) K' J₁))
  refine ⟨C', instC', J', D', instD', K', v₁ ⋙ t, w, u₁ ⋙ t, hcompDense, instw, hflC, hflD,
    hsubJ, hsubK, hcontu, hpflu, flat_of_preservesFiniteLimits _,
    Functor.isMorphismOfSites_of_preservesFiniteLimits _ K' J', fun i => ?_, hrepG,
    ⟨iso ≪≫ square.symm⟩⟩
  have : ((sheafToPresheaf J' (Type u)).obj
      ((v₁.sheafPushforwardCocontinuous (Type u) J J₁ ⋙
        t.sheafPushforwardCocontinuous (Type u) J₁ J').obj (F i))).IsRepresentable := hrepF i
  exact isRepresentable_of_natIso _
    ((sheafToPresheaf J' (Type u)).mapIso (compCocont.app (F i))).symm

open Stacks.Topos.RepresentedFunctor in
/-- **Stacks 03CK.** The addendum of Stacks 03CJ: if `f : Sh(C) → Sh(D)` is an *equivalence* of
topoi, then the two sites of the replacement may be taken to be the *same* site `(C', J')`, with
the middle morphism of topoi the identity. That is, there are a site `(C', J')` with all finite
limits and a subcanonical topology and special cocontinuous functors `v : C ⥤ C'` and
`w : D ⥤ C'` such that

1. prescribed families of sheaves `F` on `C` and `G` on `D` become representable on `C'`; and
2. the square commutes with the identity along its bottom edge, i.e. `g_* ≅ f_* ⋙ e_*`, where
   `g : Sh(C) → Sh(C')` and `e : Sh(D) → Sh(C')` are the equivalences induced by `v` and `w`.

Stacks 03CI is applied twice, as in Stacks 03CJ: first to `(D, K)` and `G`, giving `(D', K')` and
`w₀ : D ⥤ D'`; then to `(C, J)` and the family consisting of `F` together with the sheaves
`f⁻¹e⁻¹h_V^#` for `V` an object of `D'`, giving `(C', J')` and `v : C ⥤ C'`. The second family is
what makes the composite `H = g_* ∘ f⁻¹ ∘ e⁻¹ : Sh(D') → Sh(C')` carry each `h_V^#` to a
representable sheaf, so that `H` — an equivalence, since each of its three factors is one — is
read off as a functor `u : D' ⥤ C'` between the two *sites*
(`Stacks.Topos.RepresentedFunctor.representedFunctor`). That `u` is again special cocontinuous
(`Stacks.Topos.RepresentedFunctor.representedFunctor_isDenseSubsite`), so `w = w₀ ⋙ u` is, and
the morphism of topoi it induces is `H` itself; that is the commutativity of the square. -/
theorem exists_oneSided_isDenseSubsite_of_isEquivalence {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)))
    [f.pushforward.IsEquivalence] {ι : Type u} (F : ι → Sheaf J (Type u)) {κ : Type u}
    (G : κ → Sheaf K (Type u)) :
    ∃ (C' : Type u) (_ : SmallCategory C') (J' : GrothendieckTopology C') (v : C ⥤ C')
      (w : D ⥤ C') (_ : v.IsDenseSubsite J J') (_ : w.IsDenseSubsite K J')
      (_ : HasFiniteLimits C') (_ : J'.Subcanonical),
      (∀ i, ((v.sheafPushforwardCocontinuous (Type u) J J').obj (F i)).obj.IsRepresentable) ∧
      (∀ j, ((w.sheafPushforwardCocontinuous (Type u) K J').obj (G j)).obj.IsRepresentable) ∧
      Nonempty
        (v.sheafPushforwardCocontinuous (Type u) J J' ≅
          f.pushforward ⋙ w.sheafPushforwardCocontinuous (Type u) K J') := by
  classical
  -- Stacks 03CI applied to `(D, K)` and the family `G`.
  obtain ⟨D', instD', K', w₀, instw₀, hsubK, hflD, -, -, hrepG⟩ :=
    K.exists_isDenseSubsite_subcanonical_hasFiniteLimits_representable G
  let e₀ := Functor.IsDenseSubsite.morphismOfTopoi K K' w₀
  -- Stacks 03CI applied to `(C, J)` and the family `F` together with the sheaves `f⁻¹e⁻¹h_V^#`.
  let sourceFamily : ι ⊕ D' → Sheaf J (Type u) := fun a =>
    match a with
    | Sum.inl i => F i
    | Sum.inr V => (e₀.inverseImage ⋙ f.inverseImage).obj ((Sheaf.sheafifiedYoneda K').obj V)
  obtain ⟨C', instC', J', v, instv, hsubJ, hflC, -, -, hrepS⟩ :=
    J.exists_isDenseSubsite_subcanonical_hasFiniteLimits_representable sourceFamily
  let g₀ := Functor.IsDenseSubsite.morphismOfTopoi J J' v
  let H : Sheaf K' (Type u) ⥤ Sheaf J' (Type u) :=
    e₀.inverseImage ⋙ f.inverseImage ⋙ g₀.pushforward
  have : g₀.pushforward.IsEquivalence :=
    Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence J J' v
  have : e₀.pushforward.IsEquivalence :=
    Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence K K' w₀
  have : e₀.inverseImage.IsEquivalence :=
    Adjunction.isEquivalence_left_of_isEquivalence_right e₀.adj
  have : f.inverseImage.IsEquivalence :=
    Adjunction.isEquivalence_left_of_isEquivalence_right f.adj
  have : H.IsEquivalence := inferInstanceAs
    (e₀.inverseImage ⋙ f.inverseImage ⋙ g₀.pushforward).IsEquivalence
  have hH : ∀ V, IsRepresentableSheaf J' (H.obj ((Sheaf.sheafifiedYoneda K').obj V)) := by
    intro V
    refine isRepresentableSheaf_of_obj_isRepresentable J' _ ?_
    simpa [H, sourceFamily, g₀] using hrepS (Sum.inr V)
  -- The equivalence `H` read off as a functor between the two sites.
  let u := representedFunctor J' (Sheaf.sheafifiedYoneda K' ⋙ H) hH
  have : u.IsContinuous K' J' := representedFunctor_isContinuous J' K' H hH
  have : u.IsDenseSubsite K' J' := representedFunctor_isDenseSubsite J' K' H hH
  have : (w₀ ⋙ u).IsDenseSubsite K J' := Functor.isDenseSubsite_comp K K' J' w₀ u
  let e₁ := Functor.IsDenseSubsite.morphismOfTopoi K J' (w₀ ⋙ u)
  -- The morphism of topoi induced by `u` is `H`.
  let uIso : u.sheafPushforwardCocontinuous (Type u) K' J' ≅ H :=
    Adjunction.rightAdjointUniq (u.sheafAdjunctionCocontinuous (Type u) K' J')
      (H.asEquivalence.symm.toAdjunction.ofNatIsoLeft
        (Adjunction.rightAdjointUniq
          ((u.sheafAdjunctionContinuous (Type u) K' J').ofNatIsoLeft
            (representedPullbackIso J' K' H hH)) H.asEquivalence.toAdjunction).symm)
  let eIso : e₁.pushforward ≅ e₀.pushforward ⋙ H :=
    Functor.sheafPushforwardCocontinuousCompOfContinuous K K' J' w₀ u ≪≫
      Functor.isoWhiskerLeft e₀.pushforward uIso
  let eIso' : e₁.pushforward ≅ f.inverseImage ⋙ g₀.pushforward :=
    eIso ≪≫ counitCancel e₀.adj (f.inverseImage ⋙ g₀.pushforward)
  let square : f.pushforward ⋙ e₁.pushforward ≅ g₀.pushforward :=
    Functor.isoWhiskerLeft f.pushforward eIso' ≪≫ counitCancel f.adj g₀.pushforward
  refine ⟨C', instC', J', v, w₀ ⋙ u, instv, inferInstance, hflC, hsubJ,
    fun i => hrepS (Sum.inl i), fun j => ?_, ⟨square.symm⟩⟩
  refine obj_isRepresentable_of_isRepresentableSheaf J' _ ?_
  obtain ⟨V, ⟨iV⟩⟩ := isRepresentableSheaf_of_obj_isRepresentable K' _ (hrepG j)
  refine ⟨u.obj V, ⟨?_⟩⟩
  exact eIso.app (G j) ≪≫ H.mapIso iV ≪≫
    H.mapIso ((sheafifiedYonedaIsoYoneda K').app V).symm ≪≫
    (representedFunctorIso J' (Sheaf.sheafifiedYoneda K' ⋙ H) hH).app V

end MorphismOfTopoi

end
