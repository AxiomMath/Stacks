module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeTrace
public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointBaseChangePasting
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonAssociativity

/-!
# Base change of the twisted inverse image of a proper flat morphism

Formation of the base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*` of [Stacks, Tag 0AA6] is compatible
with pasting cartesian squares; together with the compatibility of `a` with restriction to opens
for `f` proper, flat and of finite presentation ([Stacks, Tag 0E4J]) this reduces its
invertibility to an affine base, where it is [Stacks, Tag 0AA8]: [Stacks, Tag 0AAB].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- **The cocycle identity of [Stacks, Tag 0D5S] for derived pullback of schemes** at the
locally small model. -/
theorem derivedPullbackCompIso_assoc_app {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (M : DerivedCategory W.Modules) :
    (derivedPullbackCompIso f g).hom.app ((derivedPullback h).obj M) ≫
        (derivedPullbackCompIso (f ≫ g) h).hom.app M =
      (derivedPullback f).map ((derivedPullbackCompIso g h).hom.app M) ≫
        (derivedPullbackCompIso f (g ≫ h)).hom.app M :=
  StacksDraft.DerivedModel.derivedPullbackCompIsoCanonical_assoc_app_locallySmall
    f.toLRSHom.toShHom g.toLRSHom.toShHom h.toLRSHom.toShHom M

/-- Transport of the composition isomorphism of derived pullback along an equality in the first
factor. -/
theorem derivedPullbackCompIso_hom_app_eqToHom_left {A B C : Scheme.{u}} {a a' : A ⟶ B}
    (b : B ⟶ C) (e : a = a') (M : DerivedCategory C.Modules) :
    (derivedPullbackCompIso a b).hom.app M ≫
        eqToHom (congrArg (fun h : A ⟶ B => (derivedPullback (h ≫ b)).obj M) e) =
      eqToHom (congrArg (fun h : A ⟶ B => (derivedPullback h).obj ((derivedPullback b).obj M)) e) ≫
        (derivedPullbackCompIso a' b).hom.app M := by
  subst e; simp

/-- Transport of the composition isomorphism of derived pullback along an equality in the second
factor. -/
theorem map_eqToHom_derivedPullbackCompIso_hom_app {A B C : Scheme.{u}} (b : A ⟶ B)
    {a a' : B ⟶ C} (e : a = a') (M : DerivedCategory C.Modules) :
    (derivedPullback b).map (eqToHom (congrArg (fun h : B ⟶ C => (derivedPullback h).obj M) e)) ≫
        (derivedPullbackCompIso b a').hom.app M =
      (derivedPullbackCompIso b a).hom.app M ≫
        eqToHom (congrArg (fun h : B ⟶ C => (derivedPullback (b ≫ h)).obj M) e) := by
  subst e; simp

/-- The diagram chase behind `derivedPullbackSquare_paste_app`, with every morphism a variable. -/
private theorem paste_chase {C C' : Type*} [Category C] [Category C'] (F : C' ⥤ C)
    {Oa Ob Oc Od Oe Of Og Oh : C} {Pa Pb Pc Pd : C'}
    {xi : Oa ⟶ Ob} {x : Ob ⟶ Oa} {p₁ : Ob ⟶ Oc} {e₂ : Oc ⟶ Od} {q₂i : Od ⟶ F.obj Pa}
    {q₂ : F.obj Pa ⟶ Od} {r₁ : Pa ⟶ Pb} {e₁ : Pb ⟶ Pc} {r₃i : Pc ⟶ Pd} {r₃ : Pd ⟶ Pc}
    {s : F.obj Pd ⟶ Oe} {P₀' : Oe ⟶ Of} {P₀'i : Of ⟶ Oe} {P₀ : Oa ⟶ Og} {Ew : Og ⟶ Of}
    {u₃ : F.obj Pc ⟶ Of} {u₂ : F.obj Pb ⟶ Oh} {e₁' : Oh ⟶ Of} {v₂ : Od ⟶ Oh}
    {v₁ : Oc ⟶ Og} {e₂' : Og ⟶ Oh}
    (hx : xi ≫ x = 𝟙 _) (hP : P₀' ≫ P₀'i = 𝟙 _) (a₃ : s ≫ P₀' = F.map r₃ ≫ u₃)
    (hr₃ : r₃i ≫ r₃ = 𝟙 _) (t₂ : F.map e₁ ≫ u₃ = u₂ ≫ e₁') (a₂ : q₂ ≫ v₂ = F.map r₁ ≫ u₂)
    (hq : q₂i ≫ q₂ = 𝟙 _) (t₁ : v₁ ≫ e₂' = e₂ ≫ v₂) (a₁ : p₁ ≫ v₁ = x ≫ P₀)
    (hE : e₂' ≫ e₁' = Ew) :
    P₀ ≫ Ew ≫ P₀'i = xi ≫ p₁ ≫ e₂ ≫ q₂i ≫ F.map (r₁ ≫ e₁ ≫ r₃i) ≫ s := by
  have key : p₁ ≫ e₂ ≫ q₂i ≫ F.map (r₁ ≫ e₁ ≫ r₃i) ≫ s ≫ P₀' = x ≫ P₀ ≫ Ew := by
    rw [a₃, F.map_comp, F.map_comp, Category.assoc, Category.assoc, ← F.map_comp_assoc r₃i r₃,
      hr₃, F.map_id, Category.id_comp, t₂, ← reassoc_of% a₂, reassoc_of% hq,
      ← reassoc_of% t₁, reassoc_of% a₁, hE]
  calc P₀ ≫ Ew ≫ P₀'i = xi ≫ (x ≫ P₀ ≫ Ew) ≫ P₀'i := by
        simp only [Category.assoc, reassoc_of% hx]
    _ = _ := by rw [← key]; simp only [Category.assoc, hP, Category.comp_id]

/-- **Pasting of the comparisons of composite derived pullbacks around two cartesian squares**,
in the ambient spelling: the comparison around the outer rectangle, built from `j' ≫ g'` and
`j ≫ g`, is the pasting of the comparisons of the two squares. -/
theorem derivedPullbackSquare_paste_app {U' V' X' Y' X Y : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (j' : U' ⟶ X') (f'' : U' ⟶ V') (j : V' ⟶ Y')
    (w₁ : g' ≫ f = f' ≫ g) (w₂ : j' ≫ f' = f'' ≫ j) (w : (j' ≫ g') ≫ f = f'' ≫ j ≫ g)
    (K : DerivedCategory Y.Modules) :
    (derivedPullbackCompIso f'' (j ≫ g)).hom.app K ≫
        eqToHom (congrArg (fun h : U' ⟶ Y => (derivedPullback h).obj K) w.symm) ≫
          (derivedPullbackCompIso (j' ≫ g') f).inv.app K =
      (derivedPullback f'').map ((derivedPullbackCompIso j g).inv.app K) ≫
        (derivedPullbackCompIso f'' j).hom.app ((derivedPullback g).obj K) ≫
        eqToHom (congrArg (fun h : U' ⟶ Y' => (derivedPullback h).obj ((derivedPullback g).obj K))
          w₂.symm) ≫
        (derivedPullbackCompIso j' f').inv.app ((derivedPullback g).obj K) ≫
        (derivedPullback j').map ((derivedPullbackCompIso f' g).hom.app K ≫
          eqToHom (congrArg (fun h : X' ⟶ Y => (derivedPullback h).obj K) w₁.symm) ≫
            (derivedPullbackCompIso g' f).inv.app K) ≫
        (derivedPullbackCompIso j' g').hom.app ((derivedPullback f).obj K) := by
  refine paste_chase (derivedPullback j')
    (show (derivedPullback f'').map ((derivedPullbackCompIso j g).inv.app K) ≫
        (derivedPullback f'').map ((derivedPullbackCompIso j g).hom.app K) = 𝟙 _ by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id])
    (Iso.hom_inv_id_app (derivedPullbackCompIso (j' ≫ g') f) K)
    (derivedPullbackCompIso_assoc_app j' g' f K)
    (Iso.inv_hom_id_app (derivedPullbackCompIso g' f) K)
    (map_eqToHom_derivedPullbackCompIso_hom_app j' w₁.symm K)
    (derivedPullbackCompIso_assoc_app j' f' g K)
    (Iso.inv_hom_id_app (derivedPullbackCompIso j' f') ((derivedPullback g).obj K))
    (derivedPullbackCompIso_hom_app_eqToHom_left g w₂.symm K)
    (derivedPullbackCompIso_assoc_app f'' j g K) ?_
  exact eqToHom_trans _ _

/-- The component at `K` of the isomorphism `quasiCoherentDerivedPullbackCongr e` induced by an
equality `e : h₁ = h₂` has underlying morphism `eqToHom`. -/
theorem quasiCoherentDerivedPullbackCongr_hom_app_hom {X Y : Scheme.{u}} {h₁ h₂ : X ⟶ Y}
    (e : h₁ = h₂) (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedPullbackCongr e).hom.app K).hom =
      eqToHom (congrArg (fun h : X ⟶ Y => (derivedPullback h).obj K.obj) e) :=
  rfl

/-- **Pasting of the comparisons of composite derived pullbacks on `D_QCoh`**: for two
commutative squares placed one above the other, with outer square along `p = j' ≫ g'` and
`q = j ≫ g`, the comparison around the outer square is the pasting of the two inner ones. -/
theorem quasiCoherentPullbackComparisonPaste {U' V' X' Y' X Y : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (j' : U' ⟶ X') (f'' : U' ⟶ V') (j : V' ⟶ Y')
    (p : U' ⟶ X) (q : V' ⟶ Y) (w₁ : g' ≫ f = f' ≫ g) (w₂ : j' ≫ f' = f'' ≫ j)
    (w : p ≫ f = f'' ≫ q) (hp : j' ≫ g' = p) (hq : j ≫ g = q) :
    Stacks.CategoryTheory.BaseChange.PullbackComparisonPaste
      (Lf := quasiCoherentDerivedPullback' f) (Lf₁ := quasiCoherentDerivedPullback' f')
      (Lf₂ := quasiCoherentDerivedPullback' f'') (G₁ := quasiCoherentDerivedPullback' g)
      (G₂ := quasiCoherentDerivedPullback' j) (Go := quasiCoherentDerivedPullback' q)
      (H₁ := quasiCoherentDerivedPullback' g') (H₂ := quasiCoherentDerivedPullback' j')
      (Ho := quasiCoherentDerivedPullback' p)
      (quasiCoherentDerivedPullbackCompIso f' g)
      (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr w₁)
      (quasiCoherentDerivedPullbackCompIso f'' j)
      (quasiCoherentDerivedPullbackCompIso j' f' ≪≫ quasiCoherentDerivedPullbackCongr w₂)
      (quasiCoherentDerivedPullbackCompIso f'' q)
      (quasiCoherentDerivedPullbackCompIso p f ≪≫ quasiCoherentDerivedPullbackCongr w)
      (quasiCoherentDerivedPullbackCongr hq.symm ≪≫
        (quasiCoherentDerivedPullbackCompIso j g).symm)
      (quasiCoherentDerivedPullbackCompIso j' g' ≪≫ quasiCoherentDerivedPullbackCongr hp) := by
  subst hp hq
  intro K
  simp only [Iso.trans_hom, quasiCoherentDerivedPullbackCongr_refl, Category.id_comp,
    Category.comp_id]
  apply ObjectProperty.hom_ext
  have h := derivedPullbackSquare_paste_app g' f' f g j' f'' j w₁ w₂ w K.obj
  simp only [Functor.map_comp, Category.assoc] at h
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Iso.trans_inv, Iso.symm_hom, quasiCoherentDerivedPullback_map_hom,
    quasiCoherentDerivedPullbackCompIso_hom_app_hom,
    quasiCoherentDerivedPullbackCompIso_inv_app_hom,
    quasiCoherentDerivedPullbackCongr_inv_app_hom,
    Functor.map_comp, Category.assoc]
  exact h

section Paste

variable {U' V' X' Y' X Y : Scheme.{u}} [CompactSpace U'] [QuasiSeparatedSpace U']
  [CompactSpace V'] [QuasiSeparatedSpace V'] [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The mate of the comparison of composite derived pullbacks around a Tor independent cartesian
square is invertible on `D_QCoh`. -/
private theorem isIso_twoSquare_natTrans_of_torIndependent {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (h : TorIndependent f g) :
    IsIso (Stacks.CategoryTheory.BaseChange.twoSquare
      (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
      (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
      (quasiCoherentDerivedPullbackCompIso f' g)
      (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w))
    := by
  have h := isIso_quasiCoherentDerivedBaseChange_natTrans
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq h
  rwa [quasiCoherentDerivedBaseChange_eq_twoSquare] at h

/-- **Two-out-of-three for the base change maps of [Stacks, Tag 0AA6] around two pasted cartesian
squares**, all three squares Tor independent. If the base change map of the second square is
invertible at `Lg^*K`, then that of the outer square is invertible at `K` exactly when `L(j')^*`
of that of the first one is. -/
theorem isIso_rightAdjointBaseChange_app_iff_of_paste_of_torIndependent {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} {j' : U' ⟶ X'} {f'' : U' ⟶ V'} {j : V' ⟶ Y'}
    {p : U' ⟶ X} {q : V' ⟶ Y} (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback j' f'' f' j)
    (sqO : IsPullback p f'' f q) (hp : j' ≫ g' = p) (hq : j ≫ g = q)
    (h₁ : TorIndependent f g) (h₂ : TorIndependent f' j) (hO : TorIndependent f q)
    (K : quasiCoherentDerivedCategory Y) :
    haveI := isIso_rightAdjointSquare_of_torIndependent sq₁ h₁
    haveI := isIso_rightAdjointSquare_of_torIndependent sq₂ h₂
    haveI := isIso_rightAdjointSquare_of_torIndependent sqO hO
    IsIso ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction f'' (isQuasicoherent_homology_derivedPullback' f'')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
        (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
        (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
        (quasiCoherentDerivedPullbackCompIso f'' j)
        (quasiCoherentDerivedPullbackCompIso j' f' ≪≫ quasiCoherentDerivedPullbackCongr sq₂.w)
        (twistedInverseImageAdjunction f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (twistedInverseImageAdjunction f''
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))).app
      ((quasiCoherentDerivedPullback' g).obj K)) →
    (IsIso ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f'' (isQuasicoherent_homology_derivedPullback' f'')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
        (quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs q))
        (quasiCoherentDerivedAdjunction p (isQuasicoherent_homology_derivedPullback' p)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs p))
        (quasiCoherentDerivedPullbackCompIso f'' q)
        (quasiCoherentDerivedPullbackCompIso p f ≪≫ quasiCoherentDerivedPullbackCongr sqO.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f''
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))).app K) ↔
      IsIso ((quasiCoherentDerivedPullback' j').map
        ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
        (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq₁.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).app K))) := by
  have hb₁ := isIso_twoSquare_natTrans_of_torIndependent sq₁ h₁
  have hb₂ := isIso_twoSquare_natTrans_of_torIndependent sq₂ h₂
  have hbO := isIso_twoSquare_natTrans_of_torIndependent sqO hO
  exact Stacks.CategoryTheory.BaseChange.isIso_rightAdjointBaseChange_app_iff_of_paste
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
    (quasiCoherentDerivedAdjunction f'' (isQuasicoherent_homology_derivedPullback' f'')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
    (quasiCoherentDerivedPullbackCompIso f' g)
    (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq₁.w)
    (quasiCoherentDerivedPullbackCompIso f'' j)
    (quasiCoherentDerivedPullbackCompIso j' f' ≪≫ quasiCoherentDerivedPullbackCongr sq₂.w)
    (quasiCoherentDerivedPullbackCompIso f'' q)
    (quasiCoherentDerivedPullbackCompIso p f ≪≫ quasiCoherentDerivedPullbackCongr sqO.w)
    (quasiCoherentDerivedPullbackCongr hq.symm ≪≫ (quasiCoherentDerivedPullbackCompIso j g).symm)
    (quasiCoherentDerivedPullbackCompIso j' g' ≪≫ quasiCoherentDerivedPullbackCongr hp)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (twistedInverseImageAdjunction f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
    (twistedInverseImageAdjunction f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
    (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
    (quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs q))
    (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
    (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
    (quasiCoherentDerivedAdjunction p (isQuasicoherent_homology_derivedPullback' p)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs p))
    (quasiCoherentPullbackComparisonPaste g' f' f g j' f'' j p q sq₁.w sq₂.w sqO.w hp hq) K

/-- **Two-out-of-three for the base change maps of [Stacks, Tag 0AA6] around two pasted cartesian
squares**, `f` flat. If the base change map of the second square is invertible at `Lg^*K`, then
that of the outer square is invertible at `K` exactly when `L(j')^*` of that of the first one is.
-/
theorem isIso_rightAdjointBaseChange_app_iff_of_paste {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {j' : U' ⟶ X'} {f'' : U' ⟶ V'} {j : V' ⟶ Y'} {p : U' ⟶ X}
    {q : V' ⟶ Y} [Flat f] (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback j' f'' f' j)
    (sqO : IsPullback p f'' f q) (hp : j' ≫ g' = p) (hq : j ≫ g = q)
    (K : quasiCoherentDerivedCategory Y) :
    haveI : Flat f' := MorphismProperty.of_isPullback sq₁ inferInstance
    haveI := isIso_rightAdjointSquare_of_torIndependent sq₁ (torIndependent_of_flat_left f g)
    haveI := isIso_rightAdjointSquare_of_torIndependent sq₂ (torIndependent_of_flat_left f' j)
    haveI := isIso_rightAdjointSquare_of_torIndependent sqO (torIndependent_of_flat_left f q)
    IsIso ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction f'' (isQuasicoherent_homology_derivedPullback' f'')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
        (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
        (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
        (quasiCoherentDerivedPullbackCompIso f'' j)
        (quasiCoherentDerivedPullbackCompIso j' f' ≪≫ quasiCoherentDerivedPullbackCongr sq₂.w)
        (twistedInverseImageAdjunction f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (twistedInverseImageAdjunction f''
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))).app
      ((quasiCoherentDerivedPullback' g).obj K)) →
    (IsIso ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f'' (isQuasicoherent_homology_derivedPullback' f'')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
        (quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs q))
        (quasiCoherentDerivedAdjunction p (isQuasicoherent_homology_derivedPullback' p)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs p))
        (quasiCoherentDerivedPullbackCompIso f'' q)
        (quasiCoherentDerivedPullbackCompIso p f ≪≫ quasiCoherentDerivedPullbackCongr sqO.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f''
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))).app K) ↔
      IsIso ((quasiCoherentDerivedPullback' j').map
        ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
        (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq₁.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).app K))) := by
  have : Flat f' := MorphismProperty.of_isPullback sq₁ inferInstance
  exact isIso_rightAdjointBaseChange_app_iff_of_paste_of_torIndependent sq₁ sq₂ sqO hp hq
    (torIndependent_of_flat_left f g) (torIndependent_of_flat_left f' j)
    (torIndependent_of_flat_left f q) K

end Paste

section Chart

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- **The base change map of [Stacks, Tag 0AA6] for `f` proper, flat and of finite presentation
is invertible over an affine chart**: over affine opens `V' ⊆ g⁻¹V`, the restriction of
`L(g')^* a(K) ⟶ a'(Lg^*K)` to `f'⁻¹V'` is invertible. -/
theorem isIso_map_rightAdjointBaseChange_app_of_isAffineOpen (sq : IsPullback g' f' f g)
    (V : Y.Opens) (hV : IsAffineOpen V) (V' : Y'.Opens) (hV' : IsAffineOpen V')
    (hVV' : V' ≤ g ⁻¹ᵁ V) (K : quasiCoherentDerivedCategory Y) :
    haveI := isIso_rightAdjointSquare_of_torIndependent sq (torIndependent_of_flat_left f g)
    IsIso ((quasiCoherentDerivedPullback' (f' ⁻¹ᵁ V').ι).map
        ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
        (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))).app K)) := by
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have : Flat f' := MorphismProperty.of_isPullback sq inferInstance
  have : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback sq inferInstance
  have sq₂ := (isPullback_morphismRestrict f' V').flip
  have sqC := (isPullback_morphismRestrict f V).flip
  have : CompactSpace (f' ⁻¹ᵁ V').toScheme := compactSpace_of_isPullback sq₂
  have : QuasiSeparatedSpace (f' ⁻¹ᵁ V').toScheme :=
    (f' ⁻¹ᵁ V').ι.isOpenEmbedding.quasiSeparatedSpace
  have : CompactSpace (f ⁻¹ᵁ V).toScheme := compactSpace_of_isPullback sqC
  have : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
    (f ⁻¹ᵁ V).ι.isOpenEmbedding.quasiSeparatedSpace
  have : IsProper (f ∣_ V) := MorphismProperty.of_isPullback sqC inferInstance
  have : Flat (f ∣_ V) := MorphismProperty.of_isPullback sqC inferInstance
  have : LocallyOfFinitePresentation (f ∣_ V) :=
    MorphismProperty.of_isPullback sqC inferInstance
  have sqO := sq₂.paste_horiz sq
  have hk : f' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    intro x hx
    change f.base (g'.base x) ∈ V
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact hVV' hx
  have hp : g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') hk ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g' :=
    Scheme.Hom.resLE_comp_ι _ _
  have hq : g.resLE V V' hVV' ≫ V.ι = V'.ι ≫ g := Scheme.Hom.resLE_comp_ι _ _
  have sqD : IsPullback (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') hk) (f' ∣_ V') (f ∣_ V)
      (g.resLE V V' hVV') := by
    refine IsPullback.of_right (by rw [hp, hq]; exact sqO) ?_ sqC
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, hq,
      ← Category.assoc, hp, Category.assoc, sq.w, ← Category.assoc, ← Category.assoc,
      morphismRestrict_ι]
  -- the outer square is invertible through the second factorization
  have hD := isIso_twistedInverseImageBaseChangeMap_app_of_flat sqD
    (torIndependent_of_flat_left (f ∣_ V) (g.resLE V V' hVV'))
    ((quasiCoherentDerivedPullback' V.ι).obj K)
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sqD
    (torIndependent_of_flat_left (f ∣_ V) (g.resLE V V' hVV'))
  have := isIso_rightAdjointSquare_of_torIndependent sqD
    (torIndependent_of_flat_left (f ∣_ V) (g.resLE V V' hVV'))
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange] at hD
  have hC := isIso_rightAdjointBaseChange_app_of_isOpenImmersion_of_flat _ _ _ _ sqC K
  have hO := (isIso_rightAdjointBaseChange_app_iff_of_paste sqC sqD sqO hp hq K hD).2
    (Functor.map_isIso _ _)
  have hB := isIso_rightAdjointBaseChange_app_of_isOpenImmersion_of_flat _ _ _ _ sq₂
    ((quasiCoherentDerivedPullback' g).obj K)
  exact (isIso_rightAdjointBaseChange_app_iff_of_paste sq sq₂ sqO rfl rfl K hB).1 hO

end Chart

/-- **[Stacks, Tag 0AAB].** Let `g : Y' ⟶ Y` be a morphism of quasi-compact and quasi-separated
schemes and `f : X ⟶ Y` proper, flat and of finite presentation, with base change
`f' : X' ⟶ Y'`. Then the base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is an
isomorphism for every `K ∈ D_QCoh(𝒪_Y)`. -/
@[stacks 0AAB]
theorem isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat {X' X Y' Y : Scheme.{u}}
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (K : quasiCoherentDerivedCategory Y) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
      (torIndependent_of_flat_left f g)
    IsIso ((twistedInverseImageBaseChangeMap g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      sq).app K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
    (torIndependent_of_flat_left f g)
  have := isIso_rightAdjointSquare_of_torIndependent sq (torIndependent_of_flat_left f g)
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sq]
  let I := {VV : Y.affineOpens × Y'.affineOpens // (VV.2 : Y'.Opens) ≤ g ⁻¹ᵁ (VV.1 : Y.Opens)}
  have hU : TopologicalSpace.IsOpenCover (fun i : I => f' ⁻¹ᵁ (i.1.2 : Y'.Opens)) := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨V, hV⟩ := (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top Y)).exists_mem
      (g.base (f'.base x))
    obtain ⟨V', hV', hxV', hV'V⟩ :=
      exists_isAffineOpen_mem_and_subset (x := f'.base x) (U := g ⁻¹ᵁ (V : Y.Opens)) hV
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(V, ⟨V', hV'⟩), hV'V⟩, hxV'⟩
  exact isIso_of_forall_isIso_quasiCoherentDerivedPullback _ hU _ fun i =>
    isIso_map_rightAdjointBaseChange_app_of_isAffineOpen sq _ i.1.1.2 _ i.1.2.2 i.2 K


end Stacks.Duality
