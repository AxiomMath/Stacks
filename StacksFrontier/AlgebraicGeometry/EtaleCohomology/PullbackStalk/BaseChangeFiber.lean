module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Lifts of a geometric point under small étale base change

Let `B` be a big étale site, let `f : T ⟶ S` be a morphism of its underlying category, and let
`x` be a geometric point of `T`. An object `V` of the small étale site of `S` has a set of
lifts of the image geometric point `f ∘ x`, and its base change `V ×_S T` has a set of lifts of
`x`; the universal property of the fibre product identifies the two. The identification is
natural in `V`, so the fibre functor of `f ∘ x` on the small étale site of `S` is the fibre
functor of `x` precomposed with base change.

This is the input for the comparison of étale stalks under inverse image: it exhibits the fibre
functor attached to the image point as the comap, along base change, of the fibre functor
attached to `x`.

## Main definitions

* `AlgebraicGeometry.geometricPointFiberBaseChangeEquiv` — the bijection between the lifts of
  `f ∘ x` to `V` and the lifts of `x` to `V ×_S T`.
* `AlgebraicGeometry.geometricPointFiberBaseChangeIso` — the same identification as a natural
  isomorphism of functors on the small étale site of `S`.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The scheme underlying a small étale base change is the chosen fibre product. -/
public theorem smallEtaleBaseChange_toScheme_obj_eq (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (V : SmallEtale B S.1 S.property) :
    (SmallEtale.toScheme B T.1 T.property).obj ((smallEtaleBaseChange B f).obj V) =
      B.inclusion.obj (pullback (Over.hom V.obj) f) :=
  rfl

/-- The structure morphism of a small étale base change is the second projection of the
chosen fibre product. -/
public theorem smallEtaleBaseChange_structure_eq (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (V : SmallEtale B S.1 S.property) :
    Over.hom ((smallEtaleBaseChange B f).obj V).obj = pullback.snd (Over.hom V.obj) f :=
  rfl

/-- The lifts of the image of a geometric point to an object of the small étale site of the
target correspond to the lifts of the point itself to the base change of that object. -/
public def geometricPointFiberBaseChangeEquiv (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.1)
    (V : SmallEtale B S.1 S.property) :
    (geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))).obj V ≃
      (geometricPointFiber B T.1 T.property x).obj ((smallEtaleBaseChange B f).obj V) := by
  letI := hasPullbacks_bigEtaleSite B
  letI := preservesPullbacks_bigEtaleSiteInclusion B
  let U := (smallEtaleBaseChange B f).obj V
  let pb := IsPullback.of_hasPullback V.obj.hom f
  let hpb := pb.map B.inclusion
  have hpbw : B.inclusion.map (pullback.fst (Over.hom V.obj) f) ≫
      B.inclusion.map (Over.hom V.obj) =
        B.inclusion.map (pullback.snd (Over.hom V.obj) f) ≫ B.inclusion.map f := by
    simpa only [← Functor.map_comp] using congrArg B.inclusion.map pb.w
  let xhom : x.source ⟶ B.inclusion.obj T := x.hom
  have hobj := smallEtaleBaseChange_toScheme_obj_eq B f V
  have hstruct := smallEtaleBaseChange_structure_eq B f V
  let castOut : (SmallEtale.toScheme B T.1 T.property).obj U ⟶
      B.inclusion.obj (pullback (Over.hom V.obj) f) := eqToHom hobj
  let castIn : B.inclusion.obj (pullback (Over.hom V.obj) f) ⟶
      (SmallEtale.toScheme B T.1 T.property).obj U := eqToHom hobj.symm
  have hcastOut : castOut ≫ B.inclusion.map (pullback.snd (Over.hom V.obj) f) =
      B.inclusion.map (Over.hom U.obj) := by
    cases hstruct
    cases hobj
    rfl
  have hcastIn : castIn ≫ B.inclusion.map (Over.hom U.obj) =
      B.inclusion.map (pullback.snd (Over.hom V.obj) f) := by
    cases hstruct
    cases hobj
    rfl
  have hcancel : castIn ≫ castOut = 𝟙 _ := by
    simp [castIn, castOut]
  have hcancel' : castOut ≫ castIn = 𝟙 _ := by
    simp [castIn, castOut]
  let liftPoint :
      (geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))).obj V →
      (geometricPointFiber B T.1 T.property x).obj U := fun p =>
    ⟨hpb.lift p.1 xhom (by simpa [GeometricPoint.map] using p.2) ≫ castIn, by
      rw [Category.assoc, hcastIn, hpb.lift_snd]⟩
  let restrictPoint :
      (geometricPointFiber B T.1 T.property x).obj U →
      (geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))).obj V := fun q =>
    ⟨q.1 ≫ castOut ≫ B.inclusion.map (pullback.fst (Over.hom V.obj) f), by
      change (q.1 ≫ castOut ≫ B.inclusion.map (pullback.fst (Over.hom V.obj) f)) ≫
          B.inclusion.map (Over.hom V.obj) = xhom ≫ B.inclusion.map f
      calc
        _ = q.1 ≫ castOut ≫
            (B.inclusion.map (pullback.fst (Over.hom V.obj) f) ≫
              B.inclusion.map (Over.hom V.obj)) := by cat_disch
        _ = q.1 ≫ castOut ≫
            (B.inclusion.map (pullback.snd (Over.hom V.obj) f) ≫ B.inclusion.map f) :=
              congrArg (fun k => q.1 ≫ castOut ≫ k) hpbw
        _ = xhom ≫ B.inclusion.map f := by
          simpa only [Category.assoc] using
            congrArg (fun k => q.1 ≫ k ≫ B.inclusion.map f) hcastOut |>.trans
              (by simpa only [Category.assoc] using
                congrArg (fun k => k ≫ B.inclusion.map f) q.2)
        _ = (x.map (B.inclusion.map f)).hom := rfl⟩
  refine ⟨liftPoint, restrictPoint, ?_, ?_⟩
  · intro p
    apply Subtype.ext
    change hpb.lift p.1 xhom
        (by simpa [GeometricPoint.map] using p.2) ≫ castIn ≫ castOut ≫
          B.inclusion.map (pullback.fst (Over.hom V.obj) f) = p.1
    calc
      _ = hpb.lift p.1 xhom (by simpa [GeometricPoint.map] using p.2) ≫
          (castIn ≫ castOut) ≫ B.inclusion.map (pullback.fst (Over.hom V.obj) f) := by
            cat_disch
      _ = hpb.lift p.1 xhom (by simpa [GeometricPoint.map] using p.2) ≫
            B.inclusion.map (pullback.fst (Over.hom V.obj) f) := by rw [hcancel]; cat_disch
      _ = p.1 := by rw [hpb.lift_fst]
  · intro q
    apply Subtype.ext
    have hcond : (q.1 ≫ castOut ≫ B.inclusion.map (pullback.fst (Over.hom V.obj) f)) ≫
        B.inclusion.map (Over.hom V.obj) = xhom ≫ B.inclusion.map f := (restrictPoint q).2
    change hpb.lift (q.1 ≫ castOut ≫ B.inclusion.map (pullback.fst (Over.hom V.obj) f))
        xhom hcond ≫ castIn = q.1
    have hlift : hpb.lift (q.1 ≫ castOut ≫ B.inclusion.map (pullback.fst (Over.hom V.obj) f))
        xhom hcond = q.1 ≫ castOut := by
      apply hpb.hom_ext
      · rw [hpb.lift_fst]
        cat_disch
      · rw [hpb.lift_snd]
        calc
          xhom = q.1 ≫ B.inclusion.map (Over.hom U.obj) := q.2.symm
          _ = q.1 ≫ (castOut ≫ B.inclusion.map (pullback.snd (Over.hom V.obj) f)) :=
            congrArg (fun k => q.1 ≫ k) hcastOut.symm
          _ = q.1 ≫ castOut ≫ B.inclusion.map (pullback.snd (Over.hom V.obj) f) := by
            cat_disch
    rw [hlift]
    calc
      _ = q.1 ≫ (castOut ≫ castIn) := by cat_disch
      _ = q.1 := by rw [hcancel']; cat_disch

/-- The correspondence of lifts is induced by the universal property of the fibre product. -/
public theorem geometricPointFiberBaseChangeEquiv_apply_val (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.1)
    (V : SmallEtale B S.1 S.property)
    (p : (geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))).obj V) :
    (geometricPointFiberBaseChangeEquiv B f x V p).1 =
      ((IsPullback.of_hasPullback V.obj.hom f).map B.inclusion).lift p.1 x.hom
        (by simpa [GeometricPoint.map] using p.2) ≫
        eqToHom (smallEtaleBaseChange_toScheme_obj_eq B f V).symm :=
  rfl

/-- Slice base change commutes with the first projection. -/
public theorem overBaseChangeMap_fst (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S)
    {V W : BigEtaleOver B S.1 S.property} (g : V ⟶ W) :
    ((Over.pullback f).map g).left ≫ pullback.fst W.hom f =
      pullback.fst V.hom f ≫ g.left := by
  exact pullback.lift_fst _ _ _

/-- Slice base change is compatible with the second projection. -/
public theorem overBaseChangeMap_snd (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S)
    {V W : BigEtaleOver B S.1 S.property} (g : V ⟶ W) :
    ((Over.pullback f).map g).left ≫ pullback.snd W.hom f =
      pullback.snd V.hom f := by
  exact pullback.lift_snd _ _ _

/-- The fibre functor of the image of a geometric point is the fibre functor of the point
itself, precomposed with small étale base change. -/
public def geometricPointFiberBaseChangeIso (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.1) :
    geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f)) ≅
      smallEtaleBaseChange B f ⋙ geometricPointFiber B T.1 T.property x := by
  letI := hasPullbacks_bigEtaleSite B
  letI := preservesPullbacks_bigEtaleSiteInclusion B
  refine NatIso.ofComponents (fun V => Equiv.toIso
    (geometricPointFiberBaseChangeEquiv B f x V)) ?_
  intro V W a
  ext p
  apply Subtype.ext
  change (geometricPointFiberBaseChangeEquiv B f x W
      ((geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))).map a p)).1 =
    ((geometricPointFiberBaseChangeEquiv B f x V p).1 ≫
      (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B f).map a))
  rw [geometricPointFiberBaseChangeEquiv_apply_val,
    geometricPointFiberBaseChangeEquiv_apply_val]
  let pbW := IsPullback.of_hasPullback W.obj.hom f
  let hpbW := pbW.map B.inclusion
  have hobjW := smallEtaleBaseChange_toScheme_obj_eq B f W
  let castOutW := eqToHom hobjW
  let pbV := IsPullback.of_hasPullback V.obj.hom f
  let hpbV := pbV.map B.inclusion
  have hobjV := smallEtaleBaseChange_toScheme_obj_eq B f V
  let castInV := eqToHom hobjV.symm
  have hcastFstV : castInV ≫ B.inclusion.map (pullback.fst (Over.hom V.obj) f) =
      B.inclusion.map (pullback.fst (Over.hom V.obj) f) := by
    apply (eqToHom_comp_iff hobjV.symm _ _).2
    cat_disch
  have hcastSndV : castInV ≫ B.inclusion.map
      (Over.hom ((smallEtaleBaseChange B f).obj V).obj) =
      B.inclusion.map (pullback.snd (Over.hom V.obj) f) := by
    apply (eqToHom_comp_iff hobjV.symm _ _).2
    cat_disch
  have hfun := smallEtaleBaseChange_comp_inclusion B f
  have hmapOver :
      (SmallEtale.inclusion B T.1 T.property).map ((smallEtaleBaseChange B f).map a) =
        (Over.pullback f).map ((SmallEtale.inclusion B S.1 S.property).map a) := by
    cases hfun
    rfl
  have hmapScheme :
      (BigEtaleOver.toScheme B T.1 T.property).map
          ((SmallEtale.inclusion B T.1 T.property).map
            ((smallEtaleBaseChange B f).map a)) =
        (BigEtaleOver.toScheme B T.1 T.property).map
          ((Over.pullback f).map ((SmallEtale.inclusion B S.1 S.property).map a)) :=
    congrArg (BigEtaleOver.toScheme B T.1 T.property).map hmapOver
  have hmapTransport : castInV ≫
      (BigEtaleOver.toScheme B T.1 T.property).map
        ((SmallEtale.inclusion B T.1 T.property).map
          ((smallEtaleBaseChange B f).map a)) ≫
      castOutW =
        (BigEtaleOver.toScheme B T.1 T.property).map
          ((Over.pullback f).map ((SmallEtale.inclusion B S.1 S.property).map a)) := by
    cases hobjV
    cases hobjW
    exact hmapScheme
  have htailFst : castInV ≫
      (BigEtaleOver.toScheme B T.1 T.property).map
        ((SmallEtale.inclusion B T.1 T.property).map
          ((smallEtaleBaseChange B f).map a)) ≫
      castOutW ≫ B.inclusion.map (pullback.fst (Over.hom W.obj) f) =
      B.inclusion.map (pullback.fst (Over.hom V.obj) f) ≫
        (BigEtaleOver.toScheme B S.1 S.property).map
          ((SmallEtale.inclusion B S.1 S.property).map a) := by
    calc
      _ = (castInV ≫
          (BigEtaleOver.toScheme B T.1 T.property).map
            ((SmallEtale.inclusion B T.1 T.property).map
              ((smallEtaleBaseChange B f).map a)) ≫
          castOutW) ≫ B.inclusion.map (pullback.fst (Over.hom W.obj) f) := by cat_disch
      _ = (BigEtaleOver.toScheme B T.1 T.property).map
          ((Over.pullback f).map ((SmallEtale.inclusion B S.1 S.property).map a)) ≫
          B.inclusion.map (pullback.fst (Over.hom W.obj) f) :=
            congrArg (fun k => k ≫ B.inclusion.map (pullback.fst (Over.hom W.obj) f))
              hmapTransport
      _ = B.inclusion.map (pullback.fst (Over.hom V.obj) f) ≫
          (BigEtaleOver.toScheme B S.1 S.property).map
            ((SmallEtale.inclusion B S.1 S.property).map a) := by
        change B.inclusion.map
            (((Over.pullback f).map ((SmallEtale.inclusion B S.1 S.property).map a)).left ≫
              pullback.fst (Over.hom W.obj) f) =
          B.inclusion.map
            (pullback.fst (Over.hom V.obj) f ≫
              ((SmallEtale.inclusion B S.1 S.property).map a).left)
        exact congrArg B.inclusion.map
          (overBaseChangeMap_fst B f ((SmallEtale.inclusion B S.1 S.property).map a))
  have htailSnd : castInV ≫
      (BigEtaleOver.toScheme B T.1 T.property).map
        ((SmallEtale.inclusion B T.1 T.property).map
          ((smallEtaleBaseChange B f).map a)) ≫
      castOutW ≫ B.inclusion.map (pullback.snd (Over.hom W.obj) f) =
      B.inclusion.map (pullback.snd (Over.hom V.obj) f) := by
    calc
      _ = (castInV ≫
          (BigEtaleOver.toScheme B T.1 T.property).map
            ((SmallEtale.inclusion B T.1 T.property).map
              ((smallEtaleBaseChange B f).map a)) ≫
          castOutW) ≫ B.inclusion.map (pullback.snd (Over.hom W.obj) f) := by cat_disch
      _ = (BigEtaleOver.toScheme B T.1 T.property).map
          ((Over.pullback f).map ((SmallEtale.inclusion B S.1 S.property).map a)) ≫
          B.inclusion.map (pullback.snd (Over.hom W.obj) f) :=
            congrArg (fun k => k ≫ B.inclusion.map (pullback.snd (Over.hom W.obj) f))
              hmapTransport
      _ = B.inclusion.map (pullback.snd (Over.hom V.obj) f) := by
        change B.inclusion.map
            (((Over.pullback f).map ((SmallEtale.inclusion B S.1 S.property).map a)).left ≫
              pullback.snd (Over.hom W.obj) f) =
          B.inclusion.map (pullback.snd (Over.hom V.obj) f)
        exact congrArg B.inclusion.map
          (overBaseChangeMap_snd B f ((SmallEtale.inclusion B S.1 S.property).map a))
  have hcondV : p.1 ≫ B.inclusion.map (Over.hom V.obj) = x.hom ≫ B.inclusion.map f := by
    simpa [GeometricPoint.map] using p.2
  have hVfst := hpbV.lift_fst p.1 x.hom hcondV
  have hVsnd := hpbV.lift_snd p.1 x.hom hcondV
  apply (cancel_mono castOutW).mp
  simp only [Category.assoc, castOutW, eqToHom_trans, eqToHom_refl]
  apply hpbW.hom_ext
  · change hpbW.lift _ _ _ ≫ B.inclusion.map (pullback.fst (Over.hom W.obj) f) = _
    rw [hpbW.lift_fst]
    change p.1 ≫ (SmallEtale.toScheme B S.1 S.property).map a =
      (hpbV.lift p.1 x.hom hcondV ≫ castInV ≫
        (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B f).map a) ≫
        castOutW) ≫ B.inclusion.map (pullback.fst (Over.hom W.obj) f)
    calc
      p.1 ≫ (SmallEtale.toScheme B S.1 S.property).map a =
          (hpbV.lift p.1 x.hom hcondV ≫
            B.inclusion.map (pullback.fst (Over.hom V.obj) f)) ≫
            (SmallEtale.toScheme B S.1 S.property).map a := by
        rw [hVfst]
      _ = hpbV.lift p.1 x.hom hcondV ≫
          (B.inclusion.map (pullback.fst (Over.hom V.obj) f) ≫
            (SmallEtale.toScheme B S.1 S.property).map a) := by cat_disch
      _ = hpbV.lift p.1 x.hom hcondV ≫
          (castInV ≫
            (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B f).map a) ≫
            castOutW ≫ B.inclusion.map (pullback.fst (Over.hom W.obj) f)) := by
        congr 1
        change B.inclusion.map (pullback.fst (Over.hom V.obj) f) ≫
            (BigEtaleOver.toScheme B S.1 S.property).map
              ((SmallEtale.inclusion B S.1 S.property).map a) =
          castInV ≫
            (BigEtaleOver.toScheme B T.1 T.property).map
              ((SmallEtale.inclusion B T.1 T.property).map
                ((smallEtaleBaseChange B f).map a)) ≫
            castOutW ≫ B.inclusion.map (pullback.fst (Over.hom W.obj) f)
        exact htailFst.symm
      _ = (hpbV.lift p.1 x.hom hcondV ≫ castInV ≫
          (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B f).map a) ≫
          castOutW) ≫ B.inclusion.map (pullback.fst (Over.hom W.obj) f) := by cat_disch
  · change hpbW.lift _ _ _ ≫ B.inclusion.map (pullback.snd (Over.hom W.obj) f) = _
    rw [hpbW.lift_snd]
    change x.hom =
      (hpbV.lift p.1 x.hom hcondV ≫ castInV ≫
        (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B f).map a) ≫
        castOutW) ≫ B.inclusion.map (pullback.snd (Over.hom W.obj) f)
    calc
      x.hom = hpbV.lift p.1 x.hom hcondV ≫
          B.inclusion.map (pullback.snd (Over.hom V.obj) f) := hVsnd.symm
      _ = hpbV.lift p.1 x.hom hcondV ≫
          (castInV ≫
            (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B f).map a) ≫
            castOutW ≫ B.inclusion.map (pullback.snd (Over.hom W.obj) f)) := by
        congr 1
        change B.inclusion.map (pullback.snd (Over.hom V.obj) f) =
          castInV ≫
            (BigEtaleOver.toScheme B T.1 T.property).map
              ((SmallEtale.inclusion B T.1 T.property).map
                ((smallEtaleBaseChange B f).map a)) ≫
            castOutW ≫ B.inclusion.map (pullback.snd (Over.hom W.obj) f)
        exact htailSnd.symm
      _ = (hpbV.lift p.1 x.hom hcondV ≫ castInV ≫
          (SmallEtale.toScheme B T.1 T.property).map ((smallEtaleBaseChange B f).map a) ≫
          castOutW) ≫ B.inclusion.map (pullback.snd (Over.hom W.obj) f) := by cat_disch

end AlgebraicGeometry

end
