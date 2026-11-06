module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsLimit

/-!
# Sections of an inverse image vanishing on a dense open

Let `f : X ⟶ Y` be a morphism of schemes and `F` an abelian sheaf on `Y_étale` such that, for
every section `h` of `F` over an étale `W ⟶ Y`, the set of points of `W` near which `h` vanishes
is closed (it is always open). Then a section of `f⁻¹ F` over an étale `U ⟶ X` which vanishes on
every étale `U`-scheme landing in a dense open `S ⊆ X` vanishes.

Locally on `U` the section is the pull-back of a section `h` of `F` over some `W` along
`U' ⟶ W ×_Y X` (`Stacks.EtaleCohomology.exists_covering_smallEtalePullbackAb_eq_unitApp`). The
points of `U'` whose image in `W` lies in the clopen vanishing locus `Z` of `h` form a clopen set
near each of whose points the section vanishes. Its complement is open; if it were nonempty it
would meet the preimage of `S`, over which the section vanishes, and then the section would vanish
near a point there through some `W' ⟶ W` on which `h` vanishes
(`Stacks.EtaleCohomology.exists_covering_of_smallEtalePullbackAb_unitApp_eq_zero`), putting the
image of that point in `Z`.

This is the germ argument behind the injectivity of the base change map `g⁻¹ j_* M ⟶ j'_* g'⁻¹ M`
used for the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), for a base change `g` which is not of finite
presentation.

## Main results

* `Stacks.EtaleCohomology.exists_mem_sieve_mem_range_left`: a covering sieve of an étale
  `X`-scheme contains an arrow through each of its points.
* `Stacks.EtaleCohomology.smallEtalePullbackAb_section_eq_zero_of_isClosed`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **A covering sieve of an étale `X`-scheme contains an arrow through each point.** -/
theorem exists_mem_sieve_mem_range_left {X : Scheme.{u}} {U : X.Etale} {R : Sieve U}
    (hR : R ∈ smallEtaleTopology X U) (x : U.left) :
    ∃ (U' : X.Etale) (d : U' ⟶ U), R d ∧ x ∈ Set.range d.left := by
  let a : Spec (.of (AlgebraicClosure (U.left.residueField x))) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x)
      (AlgebraicClosure (U.left.residueField x)))) ≫ U.left.fromSpecResidueField x
  let x₀ : (Scheme.pointSmallEtale (a ≫ U.hom)).fiber.obj U := Over.homMk a rfl
  obtain ⟨W, g, hg, yW, hyW⟩ := (Scheme.pointSmallEtale (a ≫ U.hom)).jointly_surjective R hR x₀
  let pt : Spec (.of (AlgebraicClosure (U.left.residueField x))) := default
  refine ⟨W, g, hg, yW.left pt, ?_⟩
  have hw : yW.left ≫ g.left = a := congrArg (fun φ => φ.left) hyW
  show (yW.left ≫ g.left) pt = x
  rw [hw]
  exact Scheme.fromSpecResidueField_apply x _

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A section of an abelian sheaf vanishing on a covering sieve vanishes.** -/
theorem sheafAb_section_eq_zero_of_mem {X : Scheme.{u}}
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) {V : X.Etale} (t : ToType (G.obj.obj (op V)))
    (S : Sieve V) (hS : S ∈ smallEtaleTopology X V)
    (h : ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), S g → G.obj.map g.op t = 0) : t = 0 := by
  have hG := (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1
    ((CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget (smallEtaleTopology X) G.obj
      (forget Ab.{u + 1})).1 G.property)
  refine ((hG S hS).isSeparatedFor).ext (t₁ := t) (t₂ := (0 : ToType (G.obj.obj (op V))))
    fun W g hg => ?_
  show G.obj.map g.op t = G.obj.map g.op 0
  rw [h g hg, map_zero]

/-- **A section of an abelian sheaf vanishing near every point vanishes.** -/
theorem sheafAb_section_eq_zero_of_forall_exists_mem_range {X : Scheme.{u}}
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) {V : X.Etale} (t : ToType (G.obj.obj (op V)))
    (ht : ∀ v : V.left, ∃ (V' : X.Etale) (c : V' ⟶ V), v ∈ Set.range c.left ∧
      G.obj.map c.op t = 0) :
    t = 0 := by
  let R : Sieve V :=
    { arrows := fun _ c => G.obj.map c.op t = 0
      downward_closed := fun {_ _} c hc c' => by
        rw [op_comp, G.obj.map_comp, ConcreteCategory.comp_apply, hc, map_zero] }
  refine sheafAb_section_eq_zero_of_mem G t R ?_ fun _ c hc => hc
  let ι := Σ (V' : X.Etale), {c : V' ⟶ V // R c}
  refine (smallEtaleTopology X).superset_covering (S := Sieve.ofArrows (fun x : ι => x.1)
    (fun x => x.2.1)) ?_ ((ofArrows_mem_smallEtaleTopology_iff _).2 ?_)
  · rintro _ _ ⟨_, k, _, ⟨x⟩, rfl⟩
    exact R.downward_closed x.2.2 k
  · refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨V', c, hv, hc⟩ := ht v
    exact Set.mem_iUnion.2 ⟨⟨V', c, hc⟩, hv⟩

/-- **The pull-back of a section vanishes near a point mapping into its vanishing locus.** -/
theorem exists_map_smallEtalePullbackAbUnitApp_eq_zero
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) {W : Y.Etale} (h : ToType (F.obj.obj (op W)))
    {U' : X.Etale} (m : U' ⟶ (smallEtaleBaseChange f).obj W) (u : U'.left)
    (hu : ∃ (W' : Y.Etale) (q : W' ⟶ W), (m.left ≫ pullback.fst W.hom f) u ∈ Set.range q.left ∧
      F.obj.map q.op h = 0) :
    ∃ (U'' : X.Etale) (c : U'' ⟶ U'), u ∈ Set.range c.left ∧
      ((smallEtalePullbackAb f).obj F).obj.map c.op
        (((smallEtalePullbackAb f).obj F).obj.map m.op (smallEtalePullbackAbUnitApp f F W h)) =
        0 := by
  obtain ⟨W', q, ⟨w', hw'⟩, hq⟩ := hu
  let G := (smallEtalePullbackAb f).obj F
  let B := smallEtaleBaseChange f
  let φ : U'.left ⟶ W.left := m.left ≫ pullback.fst W.hom f
  have : Etale q.left := Etale.of_comp q.left W.hom
  have : Etale U'.hom := U'.prop
  let wh : W.left ⟶ Y := W.hom
  let wh' : W'.left ⟶ Y := W'.hom
  let uh : U'.left ⟶ X := U'.hom
  let ql : W'.left ⟶ W.left := q.left
  let mL : U'.left ⟶ pullback wh f := m.left
  let bq : pullback wh' f ⟶ pullback wh f := (B.map q).left
  have h2 : ql ≫ wh = wh' := MorphismProperty.Over.w q
  have h3 : mL ≫ pullback.snd wh f = uh := MorphismProperty.Over.w m
  have hb₁ : bq ≫ pullback.fst wh f = pullback.fst wh' f ≫ ql := pullback.lift_fst _ _ _
  have hb₂ : bq ≫ pullback.snd wh f = pullback.snd wh' f := pullback.lift_snd _ _ _
  have hφ : φ = mL ≫ pullback.fst wh f := rfl
  have h1 : pullback.snd φ ql ≫ ql = pullback.fst φ ql ≫ φ := pullback.condition.symm
  have h4 : φ ≫ wh = uh ≫ f := by
    rw [hφ, Category.assoc, pullback.condition, ← Category.assoc, h3]
  have hcond : pullback.snd φ ql ≫ wh' = (pullback.fst φ ql ≫ uh) ≫ f := by
    rw [← h2, ← Category.assoc, h1, Category.assoc, h4, Category.assoc]
  let U'' : X.Etale := Scheme.Etale.mk (pullback.fst φ ql ≫ uh)
  let c : U'' ⟶ U' := MorphismProperty.Over.homMk (pullback.fst φ ql) rfl trivial
  let lf : pullback φ ql ⟶ pullback wh' f :=
    pullback.lift (pullback.snd φ ql) (pullback.fst φ ql ≫ uh) hcond
  let m₂ : U'' ⟶ B.obj W' := MorphismProperty.Over.homMk lf (pullback.lift_snd _ _ _) trivial
  have hsq : c ≫ m = m₂ ≫ B.map q := by
    refine MorphismProperty.Over.Hom.ext ?_
    show pullback.fst φ ql ≫ mL = lf ≫ bq
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hb₁, ← hφ, ← Category.assoc, pullback.lift_fst]
      exact h1.symm
    · rw [Category.assoc, Category.assoc, hb₂, h3, pullback.lift_snd]
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := ql) u w'
    hw'.symm
  refine ⟨U'', c, ⟨p, hp⟩, ?_⟩
  show G.obj.map c.op (G.obj.map m.op (smallEtalePullbackAbUnitApp f F W h)) = 0
  rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp, ← op_comp, hsq, op_comp,
    G.obj.map_comp, ConcreteCategory.comp_apply,
    ← smallEtalePullbackAbUnitApp_naturality f F q h, hq, map_zero, map_zero]

/-- **Every point maps into the vanishing locus of `h`** when that locus is closed and the
pull-back of `h` vanishes over a dense open. -/
theorem exists_map_eq_zero_of_dense (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) {W : Y.Etale}
    (h : ToType (F.obj.obj (op W)))
    (hZ : IsClosed {w : W.left | ∃ (W' : Y.Etale) (q : W' ⟶ W), w ∈ Set.range q.left ∧
      F.obj.map q.op h = 0})
    (S : X.Opens) (hS : Dense (S : Set X)) {U' : X.Etale}
    (m : U' ⟶ (smallEtaleBaseChange f).obj W)
    (hm : ∀ (U'' : X.Etale) (c : U'' ⟶ U'), Set.range U''.hom ⊆ (S : Set X) →
      ((smallEtalePullbackAb f).obj F).obj.map (c ≫ m).op
        (smallEtalePullbackAbUnitApp f F W h) = 0)
    (u : U'.left) :
    ∃ (W' : Y.Etale) (q : W' ⟶ W), (m.left ≫ pullback.fst W.hom f) u ∈ Set.range q.left ∧
      F.obj.map q.op h = 0 := by
  by_contra hu
  let B := smallEtaleBaseChange f
  let φ : U'.left ⟶ W.left := m.left ≫ pullback.fst W.hom f
  let Z : Set W.left := {w | ∃ (W' : Y.Etale) (q : W' ⟶ W), w ∈ Set.range q.left ∧
    F.obj.map q.op h = 0}
  let O : Set U'.left := φ ⁻¹' Zᶜ
  have hOo : IsOpen O := hZ.isOpen_compl.preimage φ.base.hom.continuous
  have : Etale U'.hom := U'.prop
  obtain ⟨_, ⟨o, hoO, rfl⟩, hoS⟩ : ((U'.hom '' O) ∩ (S : Set X)).Nonempty :=
    hS.inter_open_nonempty _ (U'.hom.isOpenMap _ hOo) ⟨_, u, hu, rfl⟩
  let O' : U'.left.Opens := ⟨O ∩ U'.hom ⁻¹' (S : Set X),
    hOo.inter (S.isOpen.preimage U'.hom.base.hom.continuous)⟩
  let U'' : X.Etale := Scheme.Etale.mk (O'.ι ≫ U'.hom)
  let c : U'' ⟶ U' := MorphismProperty.Over.homMk O'.ι rfl trivial
  obtain ⟨S₂, hS₂, hfac⟩ := exists_covering_of_smallEtalePullbackAb_unitApp_eq_zero f F (c ≫ m) h
    (hm U'' c (Set.range_subset_iff.2 fun y => y.2.2))
  obtain ⟨p₀, hp₀⟩ : o ∈ Set.range O'.ι := by
    rw [Scheme.Opens.range_ι]
    exact ⟨hoO, hoS⟩
  obtain ⟨U₃, d, hd, ⟨p, hp⟩⟩ := exists_mem_sieve_mem_range_left hS₂ p₀
  obtain ⟨W', q, m', hm', hq⟩ := hfac d hd
  apply hoO
  refine ⟨W', q, ⟨pullback.fst W'.hom f (m'.left p), ?_⟩, hq⟩
  have hl := congrArg (fun k => (k.left ≫ pullback.fst W.hom f) p) hm'
  change (m'.left ≫ (B.map q).left ≫ pullback.fst W.hom f) p =
    ((d ≫ c ≫ m).left ≫ pullback.fst W.hom f) p at hl
  have hb : (B.map q).left ≫ pullback.fst W.hom f = pullback.fst W'.hom f ≫ q.left :=
    pullback.lift_fst _ _ _
  rw [hb] at hl
  show (q.left) ((pullback.fst W'.hom f) (m'.left p)) = φ o
  refine hl.trans ?_
  show φ (O'.ι (d.left p)) = φ o
  rw [hp, hp₀]

/-- **A section of `f⁻¹ F` vanishing over a dense open vanishes**, when the vanishing loci of the
sections of `F` are closed. Let `S` be a dense open of `X` and `t` a section of `f⁻¹ F` over an
étale `U ⟶ X` whose restriction to every étale `U`-scheme landing in `S` is zero. If, for every
section `h` of `F` over an étale `W ⟶ Y`, the set of points of `W` near which `h` vanishes is
closed, then `t = 0`. -/
theorem smallEtalePullbackAb_section_eq_zero_of_isClosed
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (hZ : ∀ (W : Y.Etale) (h : ToType (F.obj.obj (op W))), IsClosed {w : W.left |
      ∃ (W' : Y.Etale) (q : W' ⟶ W), w ∈ Set.range q.left ∧ F.obj.map q.op h = 0})
    (S : X.Opens) (hS : Dense (S : Set X)) (U : X.Etale)
    (t : ToType (((smallEtalePullbackAb f).obj F).obj.obj (op U)))
    (ht : ∀ (U' : X.Etale) (c : U' ⟶ U), Set.range U'.hom ⊆ (S : Set X) →
      ((smallEtalePullbackAb f).obj F).obj.map c.op t = 0) :
    t = 0 := by
  obtain ⟨Sv, hSv, hrep⟩ := exists_covering_smallEtalePullbackAb_eq_unitApp f F U t
  refine sheafAb_section_eq_zero_of_mem _ t Sv hSv fun U' g hg => ?_
  obtain ⟨W, m, h, hm⟩ := hrep g hg
  rw [hm]
  refine sheafAb_section_eq_zero_of_forall_exists_mem_range _ _ fun u =>
    exists_map_smallEtalePullbackAbUnitApp_eq_zero f F h m u
      (exists_map_eq_zero_of_dense f F h (hZ W h) S hS m (fun U'' c hc => ?_) u)
  have h0 := ht U'' (c ≫ g) hc
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at h0 ⊢
  rwa [← hm]

end Stacks.EtaleCohomology

end
