module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RelationSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartedSliceFlatDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartIdentityPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartQuasiFinitePair
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothChartClosedPointDiscrete
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct

/-!
# A flat chart locally of finite presentation at a point (the chart of Stacks 06MF)

Let `𝒴₀` be an algebraic stack over `S` which is locally quasi-finite over a field-valued point
`Spec(k) ⟶ S` of the base, and let `y` be a point of `|𝒴₀|`. This file assembles the chart
construction of **Stacks 06MF** at `y`: there are a scheme `Z` of the site and a 1-morphism
`Z ⟶ 𝒴₀` which is **flat and locally of finite presentation** and whose image on points
contains `y`, together with the **quasi-finiteness datum** of that chart at the point it
produces.

The construction is the one of Stacks 06MF. Local quasi-finiteness over the field point makes
`|𝒴₀|` discrete (**Stacks 06UC**), so `y` is a finite type point and **Stacks 06FX** produces a
smooth chart `p : U ⟶ 𝒴₀` with a point `u` of `U` closed in `U` and lying over `y`. The charted
self-intersection `U ×_{𝒴₀} U` is representable by an algebraic space (**Stacks 04ZP**); an
étale surjective chart `R` of it gives two *smooth* morphisms of schemes `a, b : R ⟶ U`
(**Stacks 04SW**, `AlgebraicGeometry.Stack.chartLeg`) and an identity point `r₀` with
`a r₀ = u = b r₀` (**Stacks 04XH**). The double fibre of `(a, b)` is isolated at `r₀` because `u`
is closed in `U`
(`AlgebraicGeometry.Stack.isIsolatedPoint_asFiber_chartLeg_twoFibreProductSquare`), so the
slicing lemma produces functions `s₁, …, s_d` on an affine open `V ∋ u` vanishing at `u` whose
zero scheme, pulled back to a neighbourhood `W` of `r₀`, is flat and locally of finite
presentation over `U` along `b`. The chart is the zero scheme of the `s_i` **downstairs**, cut
down to the open image of `W`, and the two properties descend to it along the base change of
`W ⟶ V`.

The slice upstairs is moreover **quasi-finite over `U` along `b`** at the point over `r₀`: the
regular sequence cutting it is as long as the dimension of `𝒪_{b⁻¹(u), r₀}`, so the local ring
of the fibre of the slice is zero-dimensional, and the residue field at `r₀` is finite over
`κ(u)` because the pair `(a, b)` is quasi-finite and `u` is closed. That is the quasi-finiteness
datum the chart carries at the point it produces, through the covering slice.

Nothing is assumed: the statement's hypotheses are the stack, its locally quasi-finite structure
1-morphism to the field-valued point, and the point of `|𝒴₀|`.

## Main results

* `AlgebraicGeometry.mem_support_ofIdealTop_of_germ_mem_maximalIdeal`: a point at which every
  section of a list vanishes lies on the zero scheme of the list.
* `AlgebraicGeometry.exists_mono_flat_surjective_slice_of_smooth`: the slicing step of
  Stacks 06MF, packaged as the zero scheme downstairs together with the slice of the relation
  covering it.
* `AlgebraicGeometry.Stack.exists_flat_isLocallyOfFinitePresentation_chart_at_point`: the chart,
  with its quasi-finiteness datum at the produced point, and with the fibre product square which
  places that datum over the charted self-intersection.

## Implementation notes

The point of the chart is pinned, not merely asserted to exist: the conclusion carries both the
point `z₀` of the underlying scheme of `Z` and the point `zs` of `|Z|` above it, and says that
`zs`, that very point, is sent to `y`. A consumer which shrinks `Z` to an open neighbourhood of
`z₀` needs to know *which* point of `Z` lies over `y`, which `y ∈ Set.range (pointsMap c)` does
not say.

The slice has to be taken downstairs. Taking the slice of the relation itself as the chart gives
a 1-morphism which is flat and locally of finite presentation but whose source has the wrong
dimension — in the self-intersection of `𝔸¹ ⟶ Spec k` the slice upstairs is a line mapping to a
single point — and a consumer of the chart needs a source whose space of points is discrete.

The identification of the slice upstairs with the base change of the slice downstairs is
`Stacks.AlgebraicGeometry.comap_ofIdealTop`: the pullback of the ideal sheaf of a zero scheme on
an *affine* scheme is the ideal sheaf of the zero scheme of the pulled-back functions. That is
why the morphism `W ⟶ U` is factored through the affine open `V` as
`AlgebraicGeometry.Scheme.Hom.resLE`, whose flatness, local finite presentation and smoothness
are instances. The covering morphism is then
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` followed by the second projection, restricted
— again by `resLE`, so that flatness and local finite presentation stay instances — to the open
piece of the zero scheme lying over the image of `W`, which is where it is surjective and which
is open because a smooth morphism is universally open.

The two slices are placed in the site by `AlgebraicGeometry.BigFppfSite.contains_of_mono`: the
immersion of a zero scheme is a preimmersion, hence a monomorphism, and so are its composites
with the open immersions in play. The objects of the site are built directly with
`AlgebraicGeometry.siteObject`, whose underlying scheme is the given one, rather than through
`AlgebraicGeometry.Space.exists_siteObject_toScheme_map_eq`, because the covering morphism
between the two slices has to be a morphism *of the site* and the functor to schemes is not
full.

No `@[stacks]` attribute is claimed: this is the chart construction of **Stacks 06MF** at one
point, and not the whole tag.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06UC](https://stacks.math.columbia.edu/tag/06UC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

/-- **A point at which every section of a list vanishes lies on the zero scheme of the list.**
The germs generate an ideal contained in the maximal ideal of the local ring, so no section of
the list is invertible at the point, which is membership of the zero locus. -/
theorem mem_support_ofIdealTop_of_germ_mem_maximalIdeal {X : Scheme.{u}} (x : X)
    (l : List Γ(X, ⊤))
    (h : ∀ f ∈ l, X.presheaf.germ ⊤ x trivial f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    x ∈ (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList l)).support := by
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_ofIdealTop,
    Scheme.mem_zeroLocus_iff]
  intro s hs hx
  have hle : Ideal.map (X.presheaf.germ ⊤ x trivial).hom (Ideal.ofList l) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    exact h b hb
  exact (IsLocalRing.mem_maximalIdeal _).mp
    (hle (Ideal.mem_map_of_mem (X.presheaf.germ ⊤ x trivial).hom hs))
    ((X.mem_basicOpen_top s x).mp hx)

/-- A fibre product square stays one when its second projection is factored through a
monomorphism: if `P = X ×_Z Y` and `P ⟶ Y` factors as `P ⟶ Y' ⟶ Y` with `Y' ⟶ Y` a
monomorphism, then `P = X ×_Z Y'`. -/
theorem isPullback_of_mono_restrict {C : Type*} [Category C] {P X Y Y' Z : C}
    {f : P ⟶ X} {g : P ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z} (hsq : IsPullback f g h k)
    {i : Y' ⟶ Y} [Mono i] {g' : P ⟶ Y'} (hg : g' ≫ i = g) :
    IsPullback f g' h (i ≫ k) := by
  have hw : f ≫ h = g' ≫ i ≫ k := by rw [← Category.assoc, hg, hsq.w]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => hsq.lift s.fst (s.snd ≫ i) (s.condition.trans (Category.assoc _ _ _).symm))
    (fun s => hsq.lift_fst _ _ _) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · exact (cancel_mono i).mp (by rw [Category.assoc, hg, hsq.lift_snd])
  · exact hsq.hom_ext (by rw [hm₁, hsq.lift_fst])
      (by rw [hsq.lift_snd, ← hg, ← Category.assoc, hm₂])

/-- Restricting a morphism to an open containing its whole image and composing back with the open
immersion recovers the morphism. -/
theorem topIso_inv_resLE_comp_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ V) : (X.topIso.inv ≫ f.resLE V ⊤ h) ≫ V.ι = f := by
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.toIso_inv_ι,
    Category.id_comp]

/-- On an affine scheme, the pullback of the zero scheme of finitely many global sections is the
zero scheme of their pullbacks. -/
theorem comap_ofIdealTop_ofList_ofFn {X Y : Scheme.{u}} [IsAffine Y] (g : X ⟶ Y) {d : ℕ}
    (s : Fin d → Γ(Y, ⊤)) (c : Fin d → Γ(X, ⊤)) (h : ∀ i, g.appTop.hom (s i) = c i) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn s))).comap g =
      Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn c)) := by
  rw [Stacks.AlgebraicGeometry.comap_ofIdealTop g (Ideal.ofList (List.ofFn s))]
  congr 1
  rw [show (Ideal.ofList (List.ofFn s)) = Ideal.span {x | x ∈ List.ofFn s} from rfl,
    Ideal.map_span]
  refine congrArg Ideal.span (Set.ext fun x => ?_)
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_ofFn]
  constructor
  · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (h i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨s i, ⟨i, rfl⟩, h i⟩

/-- If `f x` lies outside the basic open of a section `s`, then the germ at `x` of the pullback
of `s` lies in the maximal ideal. -/
theorem germ_appLE_mem_maximalIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens}
    (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ V) (s : Γ(Y, V)) (x : X) (hx : f x ∉ Y.basicOpen s) :
    X.presheaf.germ ⊤ x trivial ((f.appLE V ⊤ e).hom s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => hx ?_
  have hw : x ∈ X.basicOpen ((f.appLE V ⊤ e).hom s) := (X.mem_basicOpen_top _ x).2 hu
  rw [Scheme.basicOpen_appLE f ⊤ V e s] at hw
  exact hw.2

/-- **The slicing step of Stacks 06MF, with the slice taken downstairs.** Let `a, b : R ⟶ U` be
smooth morphisms of schemes and let `r₀ : R` be a point at which the double fibre of `(a, b)` is
isolated. Then there are schemes `Zs` and `Ts`, monomorphisms `ιZ : Zs ⟶ U` and `j : Ts ⟶ R`, a
morphism `kk : Ts ⟶ Zs` with `kk ≫ ιZ = j ≫ a` which is flat, locally of finite presentation and
surjective, and a point `t₀` of `Ts` over `r₀`, such that `j ≫ b` is flat and locally of finite
presentation — and, as soon as `r₀` is closed in its fibre under `b`, **quasi-finite at `t₀`**.

That last conjunct is the quasi-finiteness datum of the chart at the point it produces: the
chart is `Zs ⟶ U ⟶ 𝒴₀` and `Ts` covers the base change of it along the smooth chart `U ⟶ 𝒴₀`,
so quasi-finiteness of `j ≫ b` at `t₀` is quasi-finiteness of that base change at the point
above `kk t₀`.  The extra input is carried inside the conclusion, as the hypothesis of an
implication, so that the lemma's own hypotheses are unchanged; at the charted self-intersection
of **Stacks 06MF** it is discharged by
`AlgebraicGeometry.Stack.isClosed_asFiber_chartLeg_twoFibreProductSquare`.

`Zs` is the zero scheme, inside an affine open `V ∋ a r₀` of `U`, of functions
`s₁, …, s_d ∈ Γ(U, V)` vanishing at `a r₀`, cut down to the open image of the affine
neighbourhood `W` of `r₀` that
`AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth` provides, and `Ts`
is the zero scheme in `W` of the pullbacks of the `s_i`. Since `V` is affine,
`Stacks.AlgebraicGeometry.comap_ofIdealTop` identifies `Ts` with the base change of `Zs` along
`W ⟶ V`, which makes `kk` a base change of a smooth morphism, surjective onto the piece of `Zs`
over the image of `W`.

That identification is part of the conclusion: `j` factors as `Ts ⟶ W ⟶ R` through the open
immersion of `W`, and the square formed by the two morphisms out of `Ts` against `jW ≫ a` and
`ιZ` is a **fibre product square**, so `Ts = W ×_U Zs`. A consumer reading the slice against a
chart of the target needs that square and not only the commuting triangle: the comparison of
`Ts` with the base change of the chart `Zs ⟶ 𝒴₀` along the smooth chart `U ⟶ 𝒴₀` is the base
change of the open immersion `W ⟶ R` followed by the base change of the chart
`R ⟶ U ×_{𝒴₀} U`, and both of those are read off that square. -/
theorem exists_mono_flat_surjective_slice_of_smooth {R U : Scheme.{u}}
    (a b : R ⟶ U) [Smooth a] [Smooth b] (r₀ : R)
    (hiso : IsIsolatedPoint ((b.fiberι (b r₀) ≫ a).asFiber (b.asFiber r₀))) :
    ∃ (Zs Ts : Scheme.{u}) (ιZ : Zs ⟶ U) (j : Ts ⟶ R) (kk : Ts ⟶ Zs) (t₀ : Ts),
      Mono ιZ ∧ Mono j ∧ kk ≫ ιZ = j ≫ a ∧
        Flat kk ∧ LocallyOfFinitePresentation kk ∧ Function.Surjective kk.base ∧
        Flat (j ≫ b) ∧ LocallyOfFinitePresentation (j ≫ b) ∧ j t₀ = r₀ ∧
        (IsClosed ({b.asFiber r₀} : Set (b.fiber (b r₀))) → quasiFiniteAt (j ≫ b) t₀) ∧
        ∃ (W : Scheme.{u}) (jW : W ⟶ R) (jT : Ts ⟶ W), IsOpenImmersion jW ∧ jT ≫ jW = j ∧
          IsPullback jT kk (jW ≫ a) ιZ := by
  classical
  obtain ⟨d, V, hrV, s, hVaff, hmem, W, jW, hjW, w, hWV, cf, hWaff, hjw, hcf, hflat, hlfp,
      hqf⟩ :=
    exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth a b r₀ hiso
  have := hjW
  have : IsAffine V.toScheme := hVaff
  have hVtop : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun x _ => x.2
  -- factor `jW ≫ a` through the affine open `V`
  set gV : W ⟶ V.toScheme := W.topIso.inv ≫ (jW ≫ a).resLE V ⊤ hWV with hgVdef
  have hgV : gV ≫ V.ι = jW ≫ a := topIso_inv_resLE_comp_ι _ _ _
  have hgVsmooth : Smooth gV := by
    rw [hgVdef]
    infer_instance
  -- the functions cutting the slice, read on the affine open `V`
  set sV : Fin d → Γ(V.toScheme, ⊤) := fun i => (V.ι.appLE V ⊤ hVtop).hom (s i) with hsVdef
  have key : ∀ (x : Γ(U, V)) {f g : W ⟶ U} (h : f = g) (e : (⊤ : W.Opens) ≤ f ⁻¹ᵁ V)
      (e' : (⊤ : W.Opens) ≤ g ⁻¹ᵁ V), (f.appLE V ⊤ e).hom x = (g.appLE V ⊤ e').hom x := by
    rintro x f g rfl e e'
    rfl
  have hWV2 : (⊤ : W.Opens) ≤ (gV ≫ V.ι) ⁻¹ᵁ V := by rwa [hgV]
  have hgVapp : ∀ i, gV.appTop.hom (sV i) = cf i := by
    intro i
    rw [hcf i, key (s i) hgV.symm hWV hWV2, hsVdef, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.Hom.appLE_comp_appLE gV V.ι V ⊤ (gV ⁻¹ᵁ ⊤) hVtop le_rfl)) (s i)
  -- the zero scheme downstairs and its pullback upstairs
  set D : V.toScheme.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn sV)) with hDdef
  have hcomap : D.comap gV =
      Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn cf)) :=
    comap_ofIdealTop_ofList_ofFn gV sV cf hgVapp
  rw [← hcomap] at hflat hlfp hqf
  -- the point of the slice upstairs over `r₀`
  have hgerm : ∀ f ∈ List.ofFn cf, W.presheaf.germ ⊤ w trivial f ∈
      IsLocalRing.maximalIdeal (W.presheaf.stalk w) := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    rw [hcf i]
    refine germ_appLE_mem_maximalIdeal _ hWV _ w ?_
    change a (jW w) ∉ U.basicOpen (s i)
    rw [hjw, U.mem_basicOpen (s i) (a r₀) hrV]
    exact (IsLocalRing.mem_maximalIdeal _).1 (hmem i)
  obtain ⟨t₀, ht₀⟩ : w ∈ Set.range (D.comap gV).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, hcomap]
    exact mem_support_ofIdealTop_of_germ_mem_maximalIdeal w (List.ofFn cf) hgerm
  -- the covering morphism from the slice upstairs to the slice downstairs
  set kkfull : (D.comap gV).subscheme ⟶ D.subscheme :=
    (D.comapIso gV).hom ≫ pullback.snd gV D.subschemeι with hkkfulldef
  have hkkι : kkfull ≫ D.subschemeι = (D.comap gV).subschemeι ≫ gV := by
    rw [hkkfulldef, Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  have hkkflat : Flat kkfull := by
    rw [hkkfulldef]
    infer_instance
  have hkklfp : LocallyOfFinitePresentation kkfull := by
    rw [hkkfulldef]
    infer_instance
  have hkkιpt : ∀ t, gV ((D.comap gV).subschemeι t) = D.subschemeι (kkfull t) := fun t =>
    (congrArg (· t) hkkι).symm
  have hisosurj : Function.Surjective ((D.comapIso gV).hom.base) := fun x =>
    ⟨(D.comapIso gV).inv.base x, by
      change ((D.comapIso gV).inv ≫ (D.comapIso gV).hom) x = x
      rw [Iso.inv_hom_id]
      rfl⟩
  have hrangekk : Set.range kkfull.base = D.subschemeι.base ⁻¹' Set.range gV.base := by
    rw [← Scheme.Pullback.range_snd (f := gV) (g := D.subschemeι)]
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨t, rfl⟩ := hx
      exact ⟨(D.comapIso gV).hom t, by rw [hkkfulldef]; rfl⟩
    · obtain ⟨yy, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hisosurj yy
      exact ⟨t, by rw [hkkfulldef]; rfl⟩
  -- cut the slice downstairs down to the open image of `W`
  set O : V.toScheme.Opens := ⟨Set.range gV.base, gV.isOpenMap.isOpen_range⟩ with hOdef
  set Oz : D.subscheme.Opens := D.subschemeι ⁻¹ᵁ O with hOzdef
  have hekk : (⊤ : (D.comap gV).subscheme.Opens) ≤ kkfull ⁻¹ᵁ Oz := fun t _ =>
    show D.subschemeι (kkfull t) ∈ O from ⟨(D.comap gV).subschemeι t, hkkιpt t⟩
  set kk : (D.comap gV).subscheme ⟶ Oz.toScheme :=
    (D.comap gV).subscheme.topIso.inv ≫ kkfull.resLE Oz ⊤ hekk with hkkdef
  have hkkfac : kk ≫ Oz.ι = kkfull := topIso_inv_resLE_comp_ι _ _ _
  have hkkfacpt : ∀ t, Oz.ι (kk t) = kkfull t := fun t => congrArg (· t) hkkfac
  refine ⟨Oz.toScheme, (D.comap gV).subscheme, Oz.ι ≫ D.subschemeι ≫ V.ι,
    (D.comap gV).subschemeι ≫ jW, kk, t₀, inferInstance, inferInstance,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, hkkfac, hkkι, Category.assoc, hgV, Category.assoc]
  · rw [hkkdef]
    infer_instance
  · rw [hkkdef]
    infer_instance
  · intro ζ
    obtain ⟨t, ht⟩ : Oz.ι ζ ∈ Set.range kkfull.base := by
      rw [hrangekk]
      exact ζ.2
    exact ⟨t, Subtype.ext ((hkkfacpt t).trans ht)⟩
  · rwa [Category.assoc]
  · rwa [Category.assoc]
  · change jW ((D.comap gV).subschemeι t₀) = r₀
    rw [ht₀, hjw]
  · intro hclosedfib
    rw [Category.assoc]
    exact hqf hclosedfib t₀ ht₀
  · -- the slice upstairs is the base change of the slice downstairs along `W ⟶ U`
    refine ⟨W, jW, (D.comap gV).subschemeι, hjW, rfl, ?_⟩
    have hs : IsPullback (D.comap gV).subschemeι kkfull gV D.subschemeι :=
      isPullback_of_isClosedImmersion _ _ _ _ hkkι.symm (by simp)
    have hsOz : IsPullback (D.comap gV).subschemeι kk gV (Oz.ι ≫ D.subschemeι) :=
      isPullback_of_mono_restrict hs hkkfac
    have hfin := isPullback_comp_mono hsOz V.ι
    rwa [hgV, Category.assoc] at hfin

namespace Stack

attribute [local instance] AlgebraicGeometry.Stack.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart construction of Stacks 06MF at a point.** Let `𝒴₀` be an algebraic stack over `S`
which is locally quasi-finite over a field-valued point `Spec(k) ⟶ S` of the base, and let `y` be
a point of `|𝒴₀|`. Then there are a scheme `Z` of the site, a point `z₀` of `Z`, a point `zs` of
`|Z|` above it, and a 1-morphism `Z ⟶ 𝒴₀` which is flat and locally of finite presentation and
sends `zs` to `y`.

**Stacks 06UC** makes `|𝒴₀|` discrete and **Stacks 06FX** gives the smooth chart `p : U ⟶ 𝒴₀`
with a closed point over `y`; **Stacks 04ZP** represents the self-intersection by an algebraic
space, whose étale surjective chart `R` yields the two smooth legs `a, b : R ⟶ U` of
**Stacks 04SW** and, by **Stacks 04XH**, an identity point `r₀` over that closed point.
`AlgebraicGeometry.exists_mono_flat_surjective_slice_of_smooth` cuts the slice downstairs
together with the piece of the relation covering it, and
`AlgebraicGeometry.Stack.isFlat_and_isLocallyOfFinitePresentation_chartedSlice` descends flatness
and local finite presentation to the slice downstairs.

The last conjuncts are the **quasi-finiteness datum at `z₀`**: the slice `T` of the relation, which
is flat, locally of finite presentation and surjective over `Z` and carries a point over `z₀`,
maps to the smooth chart `U` by a morphism which is locally of finite presentation and
quasi-finite at that point, and the two composites
`T ⟶ Z ⟶ 𝒴₀` and `T ⟶ U ⟶ 𝒴₀` are 2-isomorphic.  That is the base change of the chart along the
smooth chart, read on the covering slice, and it is what a consumer checking local
quasi-finiteness of the chart in the sense of Properties of Stacks, Section 04XB needs at `z₀`.
Its one input — that the identity point is closed in its fibre under the second leg — is
discharged by `AlgebraicGeometry.Stack.isClosed_asFiber_chartLeg_twoFibreProductSquare`, so
nothing is assumed.

The final conjuncts say **how that datum sits over the charted self-intersection**: the algebraic
space `F` representing `U ×_{𝒴₀} U` with an étale chart `R` of it, the factorisation
`c = ιc ≫ p` of the chart through the smooth chart, the factorisation of the quasi-finite
morphism `T ⟶ U` through an open `W` of `R` and the second leg of the self-intersection, and —
the point of it — the **fibre product square** which identifies `T` with `W ×_{a', U, ιc} Z`,
`a'` the first leg. A consumer of the quasi-finiteness datum needs that square and not only the
morphisms: it is what makes the comparison of `T` with the base change `U ×_{𝒴₀} Z` étale, which
is `AlgebraicGeometry.Stack.exists_presheafEtale_comparison_of_isPullback_relationSlice`. -/
theorem exists_flat_isLocallyOfFinitePresentation_chart_at_point
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (𝒴₀ : Stack.AlgebraicStacks.{u, w} B S hS)
    (q : 𝒴₀ ⟶ Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (hq : AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite B S hS q)
    (y : Stack.points B S hS 𝒴₀.val.val 𝒴₀.val.property) :
    ∃ (Z : BigFppfOver B S hS) (c : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴₀)
      (z₀ : (BigFppfOver.toScheme B S hS).obj Z)
      (zs : Stack.points B S hS (Stack.schemeFibredCategory B S hS Z).val
        (Stack.schemeFibredCategory B S hS Z).property),
      AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat B S hS c ∧
      AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c ∧
      Stack.pointsHomeomorphScheme B S hS Z zs = z₀ ∧
      AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap B S hS c zs = y ∧
      ∃ (Uc : BigFppfOver B S hS) (pc : Stack.schemeStack.{u, w} B S hS Uc ⟶ 𝒴₀)
        (T : BigFppfOver B S hS) (kT : T ⟶ Z) (bT : T ⟶ Uc)
        (t : (BigFppfOver.toScheme B S hS).obj T),
        AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth B S hS pc ∧
        Nonempty (Stack.schemeStackMap.{u, w} B S hS kT ≫ c ≅
          Stack.schemeStackMap.{u, w} B S hS bT ≫ pc) ∧
        Flat ((BigFppfOver.toScheme B S hS).map kT) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map kT) ∧
        Function.Surjective ((BigFppfOver.toScheme B S hS).map kT).base ∧
        (BigFppfOver.toScheme B S hS).map kT t = z₀ ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map bT) ∧
        quasiFiniteAt ((BigFppfOver.toScheme B S hS).map bT) t ∧
        ∃ (Fc : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (eFc : StacksRepresentableCFG.EquivalenceOver
            (Stack.twoFibreProductSquareAlgebraicStacks B S hS pc pc).pt.val.val.p
            (presheafOfCategories (Fc ⋙ typeToCat)).p)
          (Rc Wc : BigFppfOver B S hS) (cRc : yoneda.obj Rc ⟶ Fc)
          (ιc : Z ⟶ Uc) (jWc : Wc ⟶ Rc) (jTc : T ⟶ Wc),
          (MorphismProperty.inverseImage
            (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf cRc ∧
          Etale ((BigFppfOver.toScheme B S hS).map jWc) ∧
          c = Stack.schemeStackMap.{u, w} B S hS ιc ≫ pc ∧
          bT = jTc ≫ jWc ≫ Stack.chartLeg B S hS Uc pc
            (Stack.twoFibreProductSquareAlgebraicStacks B S hS pc pc) Fc eFc Rc cRc
            (Stack.twoFibreProductSquareAlgebraicStacks B S hS pc pc).snd ∧
          IsPullback jTc kT (jWc ≫ Stack.chartLeg B S hS Uc pc
            (Stack.twoFibreProductSquareAlgebraicStacks B S hS pc pc) Fc eFc Rc cRc
            (Stack.twoFibreProductSquareAlgebraicStacks B S hS pc pc).fst) ιc := by
  classical
  -- the space of points is discrete, so `y` carries a smooth chart with a closed point over it
  have hdisc := AlgebraicStacks.discreteTopology_points_of_isLocallyQuasiFinite
    B S hS k hk toBase q hq
  obtain ⟨U, p, z, hpsmooth, hclosed, hpz⟩ :=
    exists_isClosed_smoothChart_of_discreteTopology.{u, w} B S hS 𝒴₀ hdisc y
  -- the charted self-intersection of the chart
  have hPfp : Bicategory.IsTwoFibreProduct
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p p
  have hprep : IsRepresentableByAlgebraicSpaces B S hS p.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴₀.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) p.hom
  obtain ⟨F, hF, ⟨eF⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS (Stack.schemeStack.{u, w} B S hS U).val 𝒴₀.val
    (Stack.schemeStack.{u, w} B S hS U).val p.hom p.hom
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p).underlying
    (isTwoFibreProduct_underlying_algebraicStacks B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) hPfp)
    hprep (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  obtain ⟨R, cR, hcRsurj, hcRetale⟩ := hF.exists_atlas
  have hab := smooth_chartLeg B S hS U p (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p)
    F eF R cR hF hcRetale hpsmooth hPfp
  have : Smooth ((BigFppfOver.toScheme B S hS).map (Stack.chartLeg B S hS U p
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p).fst)) := hab.1
  have : Smooth ((BigFppfOver.toScheme B S hS).map (Stack.chartLeg B S hS U p
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p).snd)) := hab.2
  obtain ⟨r₀, har, hbr⟩ := exists_point_chartLeg_eq B S hS U p
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR hPfp hcRsurj
    (pointsHomeomorphScheme B S hS U z)
  -- slice downstairs at the identity point
  obtain ⟨Zs, Ts, ιZ, jj, kk, t₀, hιmono, hjmono, hcomm, hkflat, hklfp, hksurj,
    hbflat, hblfp, hjt, hqfslice, Ws, jWs, jTs, hjWs, hjfac, hpbs⟩ :=
    exists_mono_flat_surjective_slice_of_smooth _ _ r₀
      (isIsolatedPoint_asFiber_chartLeg_twoFibreProductSquare B S hS k hk toBase q U p F eF R cR
        hq hpsmooth hF hcRetale r₀ (by rw [hbr]; exact hclosed))
  have := hιmono
  have := hjmono
  -- the two slices as objects of the site
  have hZc : B.Contains Zs := BigFppfSite.contains_of_mono B ιZ U.left.2
  have hTc : B.Contains Ts := BigFppfSite.contains_of_mono B jj R.left.2
  set Zsite : BigFppfOver B S hS :=
    siteObject B S hS hZc (ιZ ≫ B.inclusion.map U.hom) with hZsite
  set Tsite : BigFppfOver B S hS :=
    siteObject B S hS hTc (jj ≫ B.inclusion.map R.hom) with hTsite
  set ιsite : Zsite ⟶ U := Over.homMk (ObjectProperty.homMk ιZ) rfl with hιsite
  set jsite : Tsite ⟶ R := Over.homMk (ObjectProperty.homMk jj) rfl with hjsite
  have hwk : (ObjectProperty.homMk kk : B.obj hTc ⟶ B.obj hZc) ≫ Zsite.hom = Tsite.hom := by
    refine ObjectProperty.hom_ext _ ?_
    change kk ≫ ιZ ≫ B.inclusion.map U.hom = jj ≫ B.inclusion.map R.hom
    rw [← Category.assoc, hcomm, Category.assoc]
    refine congrArg (fun m => jj ≫ m) ?_
    change B.inclusion.map (Stack.chartLeg B S hS U p
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p).fst).left ≫
      B.inclusion.map U.hom = B.inclusion.map R.hom
    rw [← B.inclusion.map_comp, Over.w]
  set ksite : Tsite ⟶ Zsite := Over.homMk (ObjectProperty.homMk kk) hwk with hksite
  -- the open of the relation through which the slice of the relation factors, in the site
  have := hjWs
  have hWc : B.Contains Ws := BigFppfSite.contains_of_mono B jWs R.left.2
  set Wsite : BigFppfOver B S hS :=
    siteObject B S hS hWc (jWs ≫ B.inclusion.map R.hom) with hWsite
  set jWsite : Wsite ⟶ R := Over.homMk (ObjectProperty.homMk jWs) rfl with hjWsite
  have hwT : (ObjectProperty.homMk jTs : B.obj hTc ⟶ B.obj hWc) ≫ Wsite.hom = Tsite.hom := by
    refine ObjectProperty.hom_ext _ ?_
    change jTs ≫ jWs ≫ B.inclusion.map R.hom = jj ≫ B.inclusion.map R.hom
    rw [← Category.assoc, hjfac]
  set jTsite : Tsite ⟶ Wsite := Over.homMk (ObjectProperty.homMk jTs) hwT with hjTsite
  have hjsitefac : jTsite ≫ jWsite = jsite :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hjfac)
  have hcommsite : ksite ≫ ιsite = jsite ≫ Stack.chartLeg B S hS U p
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p).fst :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hcomm)
  -- descend the two properties along the covering slice
  obtain ⟨hcflat, hclfp⟩ := isFlat_and_isLocallyOfFinitePresentation_chartedSlice
    B S hS U p (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR hpsmooth
    Zsite Tsite ιsite jsite ksite hcommsite hkflat hklfp (fun x => hksurj x)
    hbflat hblfp
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  let := pointTopology B S hS (schemeFibredCategory B S hS Zsite)
  have hkey : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ιsite)
      ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) = z := by
    refine (pointsHomeomorphScheme B S hS U).injective ?_
    rw [show AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ιsite)
          ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) =
        pointsMap B S hS (schemeFibredCategory B S hS Zsite).val
          (schemeFibredCategory B S hS Zsite).property
          (schemeFibredCategory B S hS U).property
          (schemeFibredCategoryMap B S hS ιsite).hom
          ((pointsHomeomorphScheme B S hS Zsite).symm (kk t₀)) from rfl,
      pointsHomeomorphScheme_naturality, Homeomorph.apply_symm_apply]
    have hc : ιZ (kk t₀) = (BigFppfOver.toScheme B S hS).map (Stack.chartLeg B S hS U p
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p).fst) (jj t₀) := by
      exact congrArg (· t₀) hcomm
    change ιZ (kk t₀) = _
    rw [hc, hjt, har]
  refine ⟨Zsite, schemeStackMap.{u, w} B S hS ιsite ≫ p, kk t₀,
    (pointsHomeomorphScheme B S hS Zsite).symm (kk t₀), hcflat, hclfp,
    (pointsHomeomorphScheme B S hS Zsite).apply_symm_apply _, ?_, ?_⟩
  · rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hkey]
    exact hpz
  -- the quasi-finiteness datum at the produced point: the slice of the relation covers the
  -- base change of the chart along the smooth chart, and is quasi-finite over `U` along `b`
  · refine ⟨U, p, Tsite, ksite, jsite ≫ Stack.chartLeg B S hS U p
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p).snd, t₀, hpsmooth, ?_,
      hkflat, hklfp, (fun x => hksurj x), rfl, ?_, ?_, F, eF, R, Wsite, cR, ιsite, jWsite,
      jTsite, hcRetale, inferInstanceAs (Etale jWs), rfl, ?_, ?_⟩
    · obtain ⟨e⟩ := nonempty_twoIso_comp_chartLeg_restrict B S hS U p
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R cR Tsite jsite
      exact ⟨(Bicategory.associator _ _ p).symm ≪≫
        eqToIso (congrArg (fun qq => qq ≫ p)
          ((schemeStackMap_comp.{u, w} B S hS ksite ιsite).trans
            (congrArg _ hcommsite))) ≪≫ e⟩
    · rwa [Functor.map_comp]
    · rw [Functor.map_comp]
      exact hqfslice (isClosed_asFiber_chartLeg_twoFibreProductSquare B S hS k hk toBase q U p
        F eF R cR hq hpsmooth hF hcRetale r₀ (by rw [hbr]; exact hclosed)
        (by rw [har]; exact hclosed))
    · rw [← Category.assoc, hjsitefac]
    · refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
      rwa [Functor.map_comp]

end Stack

end AlgebraicGeometry

end
