module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSitePresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteOfPresheaf.Coercions
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteOfPresheaf.TransitionNaturality

/-!
# The composition law of the restriction map at the charts of the members

`.memberTransitionEtaleForm_comp`, the composition law with the morphisms of charts of `X`
carried as variables; its three hypotheses at a consumer's data
(`.memberDatumRestrict_comp_apply`, `.heq_memberChartSpaceHom_postcomp`,
`.heq_memberTransitionHom_postcomp`); the composition law `.memberDatumAb_comp_apply` in the
spelling with no restriction of scalars, and `.memberDatumAb_comp_apply'`, the same law retyped
onto the sections of the presheaf of abelian groups.

The overview and the implementation notes are in the module docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteOfPresheaf/Coercions.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)


section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-! ### The composition law at the charts of the members -/

/-- **The composition law of the restriction map of the presheaf attached to a descent datum,
with the three morphisms of charts of `X` carried as variables.**  This is
`.transitionEtaleForm_base_comp` at the test spaces `chartSpace (Yi j) V'` and
`chartSpace (Yi k) V''`, the legs `memberChartMap`, the connecting morphism of charts
`.memberChartSpaceHom` and the chart `.chartSpaceIdChart`.

The three identity-and-composite morphisms of charts `idq`, `idr` and `ba` are **variables**
identified with `𝟙`, `𝟙` and `b ≫ a` by hypotheses, and the two connecting morphisms `cc` and
`e` are variables too: a consumer instantiates them with its own spellings — the ones a morphism
of the site of the charts of the members carries — and the four identifications of the
implementation notes are discharged one at a time, each in its own declaration, where each is
cheap.  Instantiating with `idq`, `idr`, `ba` *written out* instead costs four times as much to
elaborate, and the whole instantiation then exceeds the heartbeat budget.

The two test spaces are pinned by `(T := …)` and `(T' := …)` in the **`Yi`-spelling**.  They
would otherwise be inferred from `chartMap X b` in the spelling
`chartSpace X ((smallEtalePostcomp (f k) (hf k)).obj V'')`, which is the same algebraic space on
the nose and which makes **every** later identification of charts pay for that identification as
well: the instantiation times out at `isDefEq` without the pinning and takes under two
seconds with it. -/
theorem memberTransitionEtaleForm_comp (D : DescentDatum B S hS Yi f) {i j k : I}
    (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
    (V'' : SmallEtale B S hS (Yi k).1)
    (a : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V)
    (b : (smallEtalePostcomp B S hS (f k) (hf k)).obj V'' ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V')
    (idq : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') (hidq : idq = (𝟙 ((smallEtalePostcomp B S hS
        (f j) (hf j)).obj V')))
    (idr : (smallEtalePostcomp B S hS (f k) (hf k)).obj V'' ⟶
      (smallEtalePostcomp B S hS (f k) (hf k)).obj V'') (hidr : idr = (𝟙 ((smallEtalePostcomp B S hS
        (f k) (hf k)).obj V'')))
    (ba : (smallEtalePostcomp B S hS (f k) (hf k)).obj V'' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) (hba : ba = b ≫ a)
    (cc : (smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V V'' ba)
      (isEtale_memberChartMap B S hS Yi f hf V V'' ba)).obj (chartSpaceIdChart B S hS (Yi k) V'') ⟶
      (smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V V' a) (isEtale_memberChartMap B S
        hS Yi f hf V V' a)).obj (chartSpaceIdChart B S hS (Yi j) V'))
    (hcc : HEq cc ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V V' a)
      (isEtale_memberChartMap B S hS Yi f hf V V' a)).map (memberChartSpaceHom B S hS Yi f hf V' V''
      b)))
    (e : (smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V' V'' b) (isEtale_memberChartMap
      B S hS Yi f hf V' V'' b)).obj (chartSpaceIdChart B S hS (Yi k) V'') ⟶
      (smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V' V' idq) (isEtale_memberChartMap B
        S hS Yi f hf V' V' idq)).obj (chartSpaceIdChart B S hS (Yi j) V'))
    (he : HEq e ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V' V' idq)
      (isEtale_memberChartMap B S hS Yi f hf V' V' idq)).map (memberChartSpaceHom B S hS Yi f hf V'
      V'' b)))
    (W : SmallEtale B S hS (Yi i).1)
    (eg : ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V V' a)
      (isEtale_memberChartMap B S hS Yi f hf V V' a)).obj
      (chartSpaceIdChart B S hS (Yi j) V')) ⟶ W)
    (eba : ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf V V'' ba)
      (isEtale_memberChartMap B S hS Yi f hf V V'' ba)).obj
      (chartSpaceIdChart B S hS (Yi k) V'')) ⟶ W)
    (m : (D.F i).val.obj (Opposite.op W))
    (ht : (ModuleCat.Hom.hom ((D.F i).val.map eba.op) m) = (D.F i).val.map cc.op (ModuleCat.Hom.hom
      ((D.F i).val.map eg.op) m)) :
    (transitionEtaleForm B S hS Yi f D j k (memberChartPair B S hS Yi f hf V' V'' b)
          (memberChartMap B S hS Yi f hf V' V'' b)
          (memberChartMap B S hS Yi f hf V'' V'' idr)
          (isEtale_memberChartMap B S hS Yi f hf V' V'' b)
          (isEtale_memberChartMap B S hS Yi f hf V'' V'' idr)
          (memberChartPair_fst B S hS Yi f hf V' V'' b)
          (memberChartPair_snd' B S hS Yi f hf V' V'' b idr hidr)).val.app (Opposite.op
            (chartSpaceIdChart B S hS (Yi k) V''))
        (ModuleCat.Hom.hom ((D.F j).val.map e.op)
          ((transitionEtaleForm B S hS Yi f D i j (memberChartPair B S hS Yi f hf V V' a)
          (memberChartMap B S hS Yi f hf V V' a)
          (memberChartMap B S hS Yi f hf V' V' idq)
          (isEtale_memberChartMap B S hS Yi f hf V V' a)
          (isEtale_memberChartMap B S hS Yi f hf V' V' idq)
          (memberChartPair_fst B S hS Yi f hf V V' a)
          (memberChartPair_snd' B S hS Yi f hf V V' a idq hidq)).val.app (Opposite.op
            (chartSpaceIdChart B S hS (Yi j) V')) (ModuleCat.Hom.hom ((D.F i).val.map eg.op) m))) =
      (transitionEtaleForm B S hS Yi f D i k (memberChartPair B S hS Yi f hf V V'' ba)
          (memberChartMap B S hS Yi f hf V V'' ba)
          (memberChartMap B S hS Yi f hf V'' V'' idr)
          (isEtale_memberChartMap B S hS Yi f hf V V'' ba)
          (isEtale_memberChartMap B S hS Yi f hf V'' V'' idr)
          (memberChartPair_fst B S hS Yi f hf V V'' ba)
          (memberChartPair_snd' B S hS Yi f hf V V'' ba idr hidr)).val.app (Opposite.op
            (chartSpaceIdChart B S hS (Yi k) V'')) (ModuleCat.Hom.hom ((D.F i).val.map eba.op) m) :=
            by
  refine transitionEtaleForm_base_comp B S hS Yi f (T := chartSpace B S hS (Yi j) V')
    (T' := chartSpace B S hS (Yi k) V'') D (chartMap B S hS X b) (isEtale_chartMap B S hS X b) i j k
    (memberChartPair B S hS Yi f hf V V' a) (memberChartMap B S hS Yi f hf V V' a) (memberChartMap B
      S hS Yi f hf V' V' idq)
    (isEtale_memberChartMap B S hS Yi f hf V V' a) (isEtale_memberChartMap B S hS Yi f hf V' V' idq)
    (memberChartMap B S hS Yi f hf V V'' ba) (memberChartMap B S hS Yi f hf V' V'' b)
      (memberChartMap B S hS Yi f hf V'' V'' idr)
    (isEtale_memberChartMap B S hS Yi f hf V V'' ba) (isEtale_memberChartMap B S hS Yi f hf V' V''
      b) (isEtale_memberChartMap B S hS Yi f hf V'' V'' idr)
    ?_ ?_
    (memberChartPair_fst B S hS Yi f hf V V' a) (memberChartPair_snd' B S hS Yi f hf V V' a idq
      hidq)
    ?_ ?_
    (memberChartPair B S hS Yi f hf V' V'' b) (memberChartPair B S hS Yi f hf V V'' ba)
    (memberChartPair_fst B S hS Yi f hf V' V'' b) (memberChartPair_snd' B S hS Yi f hf V' V'' b idr
      hidr)
    (memberChartPair_fst B S hS Yi f hf V V'' ba) (memberChartPair_snd' B S hS Yi f hf V V'' ba idr
      hidr)
    (chartSpaceIdChart B S hS (Yi k) V'') (chartSpaceIdChart B S hS (Yi j) V') (memberChartSpaceHom
      B S hS Yi f hf V' V'' b)
    (ModuleCat.Hom.hom ((D.F i).val.map eg.op) m) (ModuleCat.Hom.hom ((D.F i).val.map eba.op) m)
    cc hcc ht e he
  all_goals subst hba hidq
  · rfl
  · rfl
  · exact (Category.assoc _ _ _).trans (congrArg _ (memberChartPair_fst B S hS Yi f hf V V' a))
  · exact (Category.assoc _ _ _).trans
      (congrArg _ (memberChartPair_snd' B S hS Yi f hf V V' a _ rfl))

/-- **Two restrictions of a component module along the morphisms of charts a morphism of the site
of the charts of the members induces compose to the restriction along the one its composite
induces.**  This is `.val_map_comp_hom_apply` at the charts of the members, where
`.memberChartSpaceHom_postcomp_comp` identifies the composite on the nose; it is the hypothesis
`ht` of `.memberTransitionEtaleForm_comp` at a consumer's own data.

Both restrictions carry their two charts explicitly, for the reason recorded at
`.memberDatumAb_comp_apply`. -/
theorem memberDatumRestrict_comp_apply (D : DescentDatum B S hS Yi f) (p q r : (MemberSite B S hS Yi
      f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (m : (D.F p.unop.1).val.obj (Opposite.op
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
      hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B
      S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))) :
      (ModuleCat.Hom.hom ((D.F p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS
      (memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫
      h).unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
      hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B
      S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
      (memberTransitionHom B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫
      h).unop)))) m) = (D.F p.unop.1).val.map ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi
      f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))).map (memberChartSpaceHom B S hS Yi f
      hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))).op (ModuleCat.Hom.hom ((D.F
      p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi
      f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi
      q.unop.1) q.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf g.unop)))) m) := (val_map_comp_hom_apply B S hS (D.F p.unop.1) (Quiver.Hom.op (X :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) (Y :=
      (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S
      hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B
      S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))
      (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)))
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi
      f hf g.unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi
      f hf h.unop))).op m).symm

/-- **The connecting restriction of charts of the source member, read at the chart the composite
morphism of the site induces.**  The two spellings are the same morphism on the nose; the content
is that the identification is performed **here**, in a declaration of its own, so that
`.memberTransitionEtaleForm_comp` is instantiated with no identification left to make. -/
theorem heq_memberChartSpaceHom_postcomp
    (p q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) : HEq
    (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf g.unop))
        (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
          g.unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f
          hf h.unop))) :
      (smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS
        Yi f hf (g ≫ h).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B
        S hS Yi f hf (g ≫ h).unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2) ⟶
      (smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
        Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
        Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
    ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf g.unop))
        (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
          g.unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f
          hf h.unop))) := HEq.rfl

/-- **The morphism of charts of the target member a morphism of the site induces is
`.memberChartSpaceHom` pushed forward along the self leg, read at the chart over which the
transition reads its target.**  This is `.memberChartSpaceHom_postcomp` with both sides retyped,
and like `.heq_memberChartSpaceHom_postcomp` its content is that the retyping happens in a
declaration of its own. -/
theorem heq_memberTransitionHom_postcomp
    (q r : (MemberSite B S hS Yi f hf)ᵒᵖ) (h : q ⟶ r) : HEq
    ((memberTransitionHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop)) :
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS
      Yi f hf h.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi
      f hf h.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)) ⟶ ((smallEtalePostcomp B
      S hS (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop))
      (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙
      q).unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))
    ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf (𝟙 q).unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom
      B S hS Yi f hf h.unop))) := HEq.rfl

/-- **THE COMPOSITION LAW of the restriction map of the presheaf attached to a descent datum, in
the spelling with no restriction of scalars**: the transition attached to a composite of two
morphisms of the site of the charts of the members, applied to the restriction of a section along
that composite, is the transition of the second applied to the restriction along it of the
transition of the first applied to the restriction along it.

Both factors are written out, in the spelling a direct `CategoryTheory.Functor` structure
instance leaves in the goal of `map_comp`.  **Every restriction carries its two charts
explicitly**, as `Quiver.Hom.op (X := …) (Y := …)`: the chart over which the transition from `p`
to `q` reads its target is the chart the *identity* morphism of the site at `q` induces, which is
the source chart `q.unop.2` on the nose, and identifying the two **inside the implicit arguments
of `CategoryTheory.Functor.map`** is unaffordable — with the restriction spelled
`(memberTransitionHom …).op`, whose implicit charts the elaborator reads off its natural type,
the instantiation below exhausts the recursion depth, and the `rfl` equation between the two
spellings exhausts the heartbeat budget on its own.  The presheaf to be assembled therefore
spells its restriction map that way, and the sections over an object of the site are read over
the chart of the identity morphism rather than over the chart itself.

**All four charts carry one and the same spelling**, the written-out
`smallEtalePostcomp (memberChartMap …) … |>.obj (chartSpaceIdChart …)`, which is what the
restriction map of the presheaf — being uniform in the morphism of the site — can spell.  That
the abbreviation `.memberTransitionChart` is *not* available here, and why the written-out
spelling costs nothing, is recorded in the implementation notes. -/
theorem memberDatumAb_comp_apply (D : DescentDatum B S hS Yi f) (p q r : (MemberSite B S hS Yi f
      hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (m : (D.F p.unop.1).val.obj (Opposite.op (((smallEtalePostcomp
      B S hS (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
      p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))))) : (transitionEtaleForm B
      S hS Yi f D q.unop.1 r.unop.1 (memberChartPair B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S
      hS Yi f hf h.unop)) (memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop)) (memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙
      r).unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop)) (isEtale_memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙
      r).unop)) (memberChartPair_fst B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop)) (memberChartPair_snd' B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop) (memberHom B S hS Yi f hf (𝟙 r).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart B
      S hS (Yi r.unop.1) r.unop.2)) (ModuleCat.Hom.hom ((D.F q.unop.1).val.map (Quiver.Hom.op (X :=
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS
      Yi f hf h.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi
      f hf h.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))) (Y :=
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf (𝟙 q).unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))
      (memberTransitionHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))))
      ((transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
      (memberHom B S hS Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) (ModuleCat.Hom.hom ((D.F
      p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi
      f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi
      q.unop.1) q.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf g.unop)))) m))) = (transitionEtaleForm B S hS Yi f D p.unop.1 r.unop.1
      (memberChartPair B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop))
      (memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop))
      (memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙 r).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫
      h).unop)) (isEtale_memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      (𝟙 r).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      (g ≫ h).unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f
      hf (g ≫ h).unop) (memberHom B S hS Yi f hf (𝟙 r).unop) rfl)).val.app (Opposite.op
      (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)) (ModuleCat.Hom.hom ((D.F p.unop.1).val.map
      (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2
      r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop)) (isEtale_memberChartMap B S hS Yi f hf
      p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop))).obj (chartSpaceIdChart B S hS (Yi
      r.unop.1) r.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS
      Yi f hf (g ≫ h).unop)))) m) := memberTransitionEtaleForm_comp B S hS Yi f hf (i := p.unop.1)
      (j := q.unop.1) (k := r.unop.1) D p.unop.2 q.unop.2 r.unop.2 (memberHom B S hS Yi f hf g.unop)
      (memberHom B S hS Yi f hf h.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl (memberHom B S hS
      Yi f hf (𝟙 r).unop) rfl (memberHom B S hS Yi f hf (g ≫ h).unop) rfl ((smallEtalePostcomp B S
      hS (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf
      g.unop))).map (memberChartSpaceHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop))) (heq_memberChartSpaceHom_postcomp B S hS Yi f hf p q r g h) (memberTransitionHom B S
      hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))
      (heq_memberTransitionHom_postcomp B S hS Yi f hf q r h) (((smallEtalePostcomp B S hS
      (memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙
      p).unop))).obj (chartSpaceIdChart B S hS (Yi p.unop.1) p.unop.2))) (memberTransitionHom B S hS
      Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberTransitionHom B S hS Yi f
      hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop)) m
      (memberDatumRestrict_comp_apply B S hS Yi f hf D p q r g h m)



/-! ### The sections of the presheaf of abelian groups, and the composition law on them -/

/-- **The composition law of the restriction map, retyped onto the sections of the presheaf of
abelian groups.**  `.memberDatumAb_comp_apply` states the law at the type its own two sides
carry, which is the sections of an étale restriction over the identity chart of a chart space,
while the sections of the presheaf of abelian groups to be assembled are the sections of the
component module over the chart which the identity morphism of the site induces.  The two are
the same type definitionally and not syntactically, and the crossing between them is performed
here, in a declaration of its own, because anywhere else it is one identification too many:
performed inside a `map_comp` goal of a `CategoryTheory.Functor` structure instance it
exhausts the recursion depth, and a type ascription at that point does not help. -/
theorem memberDatumAb_comp_apply' (D : DescentDatum B S hS Yi f) (p q r : (MemberSite B S hS Yi f
      hf)ᵒᵖ) (g : p ⟶ q) (h : q ⟶ r) (m : memberDatumObj B S hS Yi f hf D p) : @Eq
      ↥(memberDatumObj B S hS Yi f hf D r) ( (transitionEtaleForm B S hS Yi f D q.unop.1 r.unop.1
      (memberChartPair B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))
      (memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))
      (memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙 r).unop))
      (isEtale_memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))
      (isEtale_memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙
      r).unop)) (memberChartPair_fst B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop)) (memberChartPair_snd' B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      h.unop) (memberHom B S hS Yi f hf (𝟙 r).unop) rfl)).val.app (Opposite.op (chartSpaceIdChart B
      S hS (Yi r.unop.1) r.unop.2)) (ModuleCat.Hom.hom ((D.F q.unop.1).val.map (Quiver.Hom.op (X :=
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS
      Yi f hf h.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi
      f hf h.unop))).obj (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2))) (Y :=
      ((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S
      hS Yi f hf (𝟙 q).unop))).obj (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))
      (memberTransitionHom B S hS Yi f hf q.unop.2 r.unop.2 (memberHom B S hS Yi f hf h.unop))))
      ((transitionEtaleForm B S hS Yi f D p.unop.1 q.unop.1 (memberChartPair B S hS Yi f hf p.unop.2
      q.unop.2 (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom
      B S hS Yi f hf (𝟙 q).unop)) (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
      (memberHom B S hS Yi f hf (𝟙 q).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) (ModuleCat.Hom.hom ((D.F
      p.unop.1).val.map (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi
      f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))).obj (chartSpaceIdChart B S hS (Yi
      q.unop.1) q.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS
      Yi f hf g.unop)))) m)))) ( (transitionEtaleForm B S hS Yi f D p.unop.1 r.unop.1
      (memberChartPair B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop))
      (memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop))
      (memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf (𝟙 r).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫
      h).unop)) (isEtale_memberChartMap B S hS Yi f hf r.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      (𝟙 r).unop)) (memberChartPair_fst B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f hf
      (g ≫ h).unop)) (memberChartPair_snd' B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS Yi f
      hf (g ≫ h).unop) (memberHom B S hS Yi f hf (𝟙 r).unop) rfl)).val.app (Opposite.op
      (chartSpaceIdChart B S hS (Yi r.unop.1) r.unop.2)) (ModuleCat.Hom.hom ((D.F p.unop.1).val.map
      (Quiver.Hom.op (X := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf p.unop.2
      r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop)) (isEtale_memberChartMap B S hS Yi f hf
      p.unop.2 r.unop.2 (memberHom B S hS Yi f hf (g ≫ h).unop))).obj (chartSpaceIdChart B S hS (Yi
      r.unop.1) r.unop.2)))) (Y := (((smallEtalePostcomp B S hS (memberChartMap B S hS Yi f hf
      p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop)) (isEtale_memberChartMap B S hS Yi f
      hf p.unop.2 p.unop.2 (memberHom B S hS Yi f hf (𝟙 p).unop))).obj (chartSpaceIdChart B S hS (Yi
      p.unop.1) p.unop.2)))) (memberTransitionHom B S hS Yi f hf p.unop.2 r.unop.2 (memberHom B S hS
      Yi f hf (g ≫ h).unop)))) m)) := memberDatumAb_comp_apply B S hS Yi f hf D p q r g h m

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
