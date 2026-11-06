module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle

/-!
# Square functoriality of the cotangent complex is compatible with composition

For commutative squares of homomorphisms of sheaves of commutative rings on a site, the
square functoriality of the cotangent complex (the canonical map of standard resolutions
`P_• ⟶ P'_•` and the induced `B`-linear map of cotangent complexes `L_{B/A} ⟶ L_{B'/A'}`) is
compatible with composition of squares. The map of cotangent complexes of a commutative square
`g ≫ β = α ≫ a` factors through the two canonical arrows of the triangle of Tag 08SZ.

## Main definitions

* `CategoryTheory.Sheaf.ResolutionSquareMap.comp` composes maps of standard resolutions over two
  composable squares.
* `CategoryTheory.Sheaf.towerCotangentUnit` is the unit `L_{B/A} ⟶ L_{B/A} ⊗_B D` of
  extension–restriction of scalars along `B ⟶ D`, degreewise `x ↦ 1 ⊗ x`, into the first vertex
  of the triangle of Tag 08SZ read over `B`.

## Main results

* `CategoryTheory.Sheaf.squareCotangentComplexMap_comp`: the map of cotangent complexes of a
  composite of maps of standard resolutions is the composite of the two maps, the second read
  over `B` by restriction of scalars.
* `CategoryTheory.Sheaf.resolutionSquareMap_resolution_comp` and
  `CategoryTheory.Sheaf.resolutionSquareMap_comp`: the canonical maps of standard resolutions
  compose.
* `CategoryTheory.Sheaf.squareCotangentComplexMap_resolutionSquareMap_comp`: the canonical maps
  of cotangent complexes compose.
* `CategoryTheory.Sheaf.towerCotangentUnit_comp_towerCotangentBaseChange`: the first arrow of
  Tag 08SZ is the transpose of the map of cotangent complexes of the square `(𝟙 A, h)`.
* `CategoryTheory.Sheaf.squareCotangentComplexMap_eq_towerCotangent`: for a commutative square
  `g ≫ β = α ≫ a`, the map of cotangent complexes attached to it is the unit along `β`
  followed by the restriction of scalars of the first arrow of the tower `A₀ ⟶ B₀ ⟶ B`, the
  identification `L_{g ≫ β} = L_{α ≫ a}` and the second arrow of the tower `A₀ ⟶ A ⟶ B`.

## References

* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Section 08UQ](https://stacks.math.columbia.edu/tag/08UQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

section AdjointSquare

variable {S : Type u₁} [Category.{v₁} S] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
  {F : S ⥤ D} {U : D ⥤ S} {F' : S ⥤ E} {U' : E ⥤ S} {F'' : S ⥤ E'} {U'' : E' ⥤ S}
  {K : E ⥤ D} {K' : E' ⥤ E} {K'' : E' ⥤ D}

/-- The comparison of comonads is compatible with composition of squares of adjunctions: along
a comparison `K'' ⟶ K' ⋙ K` of the functors identifying the right adjoints, the comparison
attached to `K''` is the composite of the comparisons attached to `K` and to `K'`. -/
lemma Adjunction.comonadSquareHom_comp (adj : F ⊣ U) (adj' : F' ⊣ U') (adj'' : F'' ⊣ U'')
    (i : K ⋙ U ≅ U') (i' : K' ⋙ U' ≅ U'') (i'' : K'' ⋙ U ≅ U'') (c : K'' ⟶ K' ⋙ K)
    (hc : ∀ Z, U.map (c.app Z) ≫ i.hom.app (K'.obj Z) ≫ i'.hom.app Z = i''.hom.app Z)
    (Z : E') :
    (Adjunction.comonadSquareHom adj adj'' i'').app Z ≫ c.app (F''.obj (U''.obj Z)) =
      F.map (U.map (c.app Z)) ≫ (Adjunction.comonadSquareHom adj adj' i).app (K'.obj Z) ≫
        K.map ((Adjunction.comonadSquareHom adj' adj'' i').app Z) := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  have h1 := adj.unit_comp_map_comonadSquareHom adj'' i'' Z
  have h2 := adj.unit_comp_map_comonadSquareHom adj' i (K'.obj Z)
  have h3 := adj'.unit_comp_map_comonadSquareHom adj'' i' Z
  have h4 := adj.unit_naturality (U.map (c.app Z))
  have h5 := i.inv.naturality ((Adjunction.comonadSquareHom adj' adj'' i').app Z)
  have h6 : U.map (c.app (F''.obj (U''.obj Z))) =
      i''.hom.app _ ≫ i'.inv.app _ ≫ i.inv.app (K'.obj (F''.obj (U''.obj Z))) := by
    simp [← hc]
  have h7 : U.map (c.app Z) = i''.hom.app Z ≫ i'.inv.app Z ≫ i.inv.app (K'.obj Z) := by
    simp [← hc]
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h1 h2 h3 h4 h5 h6 h7 ⊢
  rw [Functor.map_comp, ← Category.assoc, h1, h6, Functor.map_comp, Functor.map_comp,
    ← Category.assoc (adj.unit.app _), h4]
  simp only [Category.assoc]
  rw [reassoc_of% h2, ← h5, reassoc_of% h3, h7]
  simp

end AdjointSquare

/-- The comparison `Under.map (f ≫ g) ≅ Under.map g ⋙ Under.map f` is the identity on the
underlying objects. -/
@[simp]
lemma Under.mapComp_hom_app_right {T : Type u₁} [Category.{v₁} T] {X Y W : T} (f : X ⟶ Y)
    (g : Y ⟶ W) (Z : Under W) : ((Under.mapComp f g).hom.app Z).right = 𝟙 Z.right := by
  simp only [Under.mapComp, eqToIso.hom, eqToHom_app, Under.eqToHom_right]
  rfl

section Iterate

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
  {E' : Type u₃} [Category.{v₃} E']
  {G : D ⥤ D} {G' : E ⥤ E} {G'' : E' ⥤ E'} {K : E ⥤ D} {K' : E' ⥤ E} {K'' : E' ⥤ D}

/-- Iterated comparisons of commuting endofunctors are compatible with composition: if the
comparison attached to `K''` is the composite of those attached to `K` and to `K'` along
`c : K'' ⟶ K' ⋙ K`, then so are their iterates. -/
lemma Functor.iterateCompHom_comp (e : K ⋙ G ⟶ G' ⋙ K) (e' : K' ⋙ G' ⟶ G'' ⋙ K')
    (e'' : K'' ⋙ G ⟶ G'' ⋙ K'') (c : K'' ⟶ K' ⋙ K)
    (he : ∀ Z, e''.app Z ≫ c.app (G''.obj Z) =
      G.map (c.app Z) ≫ e.app (K'.obj Z) ≫ K.map (e'.app Z)) (n : ℕ) (Z : E') :
    (Functor.iterateCompHom e'' n).app Z ≫ c.app ((G''.iterate n).obj Z) =
      (G.iterate n).map (c.app Z) ≫ (Functor.iterateCompHom e n).app (K'.obj Z) ≫
        K.map ((Functor.iterateCompHom e' n).app Z) := by
  induction n generalizing Z with
  | zero => simp [Functor.iterateCompHom, Functor.iterate]
  | succ n ih =>
    have hn := e.naturality ((Functor.iterateCompHom e' n).app Z)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [Functor.iterateCompHom_succ_app, Functor.iterateCompHom_succ_app,
      Functor.iterateCompHom_succ_app, Category.assoc,
      show e''.app _ ≫ c.app ((G''.iterate (n + 1)).obj Z) = _ from he ((G''.iterate n).obj Z),
      ← Category.assoc (G.map _), ← G.map_comp, ih]
    simp only [G.map_comp, Category.assoc, K.map_comp]
    rw [reassoc_of% hn]
    rfl

/-- The transported iterated comparisons are compatible with composition. -/
lemma Functor.iterateCompHomObj_comp (e : K ⋙ G ⟶ G' ⋙ K) (e' : K' ⋙ G' ⟶ G'' ⋙ K')
    (e'' : K'' ⋙ G ⟶ G'' ⋙ K'') (c : K'' ⟶ K' ⋙ K)
    (he : ∀ Z, e''.app Z ≫ c.app (G''.obj Z) =
      G.map (c.app Z) ≫ e.app (K'.obj Z) ≫ K.map (e'.app Z)) (n : ℕ)
    {X : D} {Z₁ : E} {Z₂ : E'} (u : X ⟶ K.obj Z₁) (u' : Z₁ ⟶ K'.obj Z₂)
    (u'' : X ⟶ K''.obj Z₂) (hu : u'' ≫ c.app Z₂ = u ≫ K.map u') :
    Functor.iterateCompHomObj e'' n u'' ≫ c.app ((G''.iterate n).obj Z₂) =
      Functor.iterateCompHomObj e n u ≫ K.map (Functor.iterateCompHomObj e' n u') := by
  have hn := (Functor.iterateCompHom e n).naturality u'
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.iterateCompHomObj, Category.assoc, K.map_comp]
  rw [Functor.iterateCompHom_comp e e' e'' c he n Z₂, ← Category.assoc ((G.iterate n).map u''),
    ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, reassoc_of% hn]

/-- Transported morphisms are compatible with composition along a comparison
`c : K'' ⟶ K' ⋙ K`, when the untransported ones are. -/
lemma Functor.transportObjHom_comp (c : K'' ⟶ K' ⋙ K) {X X' : D} {Y Y' : E} {W W' : E'}
    (p : X = X') (q : Y = Y') (q' : W = W') (φ : X' ⟶ K.obj Y') (φ' : Y' ⟶ K'.obj W')
    (φ'' : X' ⟶ K''.obj W') (h : φ'' ≫ c.app W' = φ ≫ K.map φ') :
    Functor.transportObjHom K'' p q' φ'' ≫ c.app W =
      Functor.transportObjHom K p q φ ≫ K.map (Functor.transportObjHom K' q q' φ') := by
  subst p q q'
  simpa [Functor.transportObjHom] using h

end Iterate

end CategoryTheory

namespace CategoryTheory.Sheaf

universe u v w

section Resolution

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A A' A'' B B' B'' : Sheaf J CommRingCat.{max u v w}}
  {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}

/-- Reading a sheaf of `A''`-algebras over `A` along `a ≫ a'` or along `a'` and then `a` gives the
same underlying sheaf of sets, and the comparison `Under.mapComp` is the identity on it. -/
lemma forgetAlgebraSheaf_map_mapComp_hom_app (a : A ⟶ A') (a' : A' ⟶ A'') (Z : Under A'') :
    (forgetAlgebraSheaf.{v, u, w} J A).map ((Under.mapComp a a').hom.app Z) = 𝟙 _ := by
  show (sheafForget J).map ((Under.mapComp a a').hom.app Z).right = _
  rw [Under.mapComp_hom_app_right]
  exact (sheafForget J).map_id _

/-- The comparison of free–forgetful comonads attached to `a ≫ a'` is the composite of the
comparisons attached to `a` and to `a'`, read through `Under.mapComp`. -/
lemma standardResolutionComonadSquareHom_comp (a : A ⟶ A') (a' : A' ⟶ A'') (Z : Under A'') :
    (standardResolutionComonadSquareHom.{u, v, w} J (a ≫ a')).app Z ≫
        (Under.mapComp a a').hom.app
          ((standardResolutionComonad.{v, u, w} J A'' : Under A'' ⥤ Under A'').obj Z) =
      (standardResolutionComonad.{v, u, w} J A : Under A ⥤ Under A).map
          ((Under.mapComp a a').hom.app Z) ≫
        (standardResolutionComonadSquareHom.{u, v, w} J a).app ((squareAlgebras J a').obj Z) ≫
          (squareAlgebras J a).map ((standardResolutionComonadSquareHom.{u, v, w} J a').app Z) :=
  Adjunction.comonadSquareHom_comp (K := squareAlgebras J a) (K' := squareAlgebras J a')
    (K'' := squareAlgebras J (a ≫ a')) (F := freeAlgebraSheaf.{v, u, w} J A)
    (U := forgetAlgebraSheaf.{v, u, w} J A) (F' := freeAlgebraSheaf.{v, u, w} J A')
    (U' := forgetAlgebraSheaf.{v, u, w} J A') (F'' := freeAlgebraSheaf.{v, u, w} J A'')
    (U'' := forgetAlgebraSheaf.{v, u, w} J A'')
    (freeAlgebraSheafAdjunction.{v, u, w} J A) (freeAlgebraSheafAdjunction.{v, u, w} J A')
    (freeAlgebraSheafAdjunction.{v, u, w} J A'') (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Under.mapComp a a').hom
    (fun Z => by
      rw [forgetAlgebraSheaf_map_mapComp_hom_app.{u, v, w} J a a' Z]
      rfl) Z

/-- The termwise maps of standard resolutions are compatible with composition of squares, as
morphisms of sheaves of `A`-algebras read through `Under.mapComp`. -/
lemma squareResolutionTermMap_comp_mapComp (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    (a' : A' ⟶ A'') (b' : B' ⟶ B'') (hsq' : f' ≫ b' = a' ≫ f'')
    (hsq'' : f ≫ b ≫ b' = (a ≫ a') ≫ f'') (n : ℕ) :
    squareResolutionTermMap.{u, v, w} J (a ≫ a') (b ≫ b') hsq'' n ≫
        (Under.mapComp a a').hom.app ((standardResolution.{v, u, w} J f'').left.obj (op ⦋n⦌)) =
      squareResolutionTermMap.{u, v, w} J a b hsq n ≫
        (squareAlgebras J a).map (squareResolutionTermMap.{u, v, w} J a' b' hsq' n) :=
  Functor.transportObjHom_comp (Under.mapComp a a').hom
    (standardResolution_obj.{v, u, w} J f n) (standardResolution_obj.{v, u, w} J f' n)
    (standardResolution_obj.{v, u, w} J f'' n) _ _ _
    (Functor.iterateCompHomObj_comp (standardResolutionComonadSquareHom.{u, v, w} J a)
      (standardResolutionComonadSquareHom.{u, v, w} J a')
      (standardResolutionComonadSquareHom.{u, v, w} J (a ≫ a')) (Under.mapComp a a').hom
      (standardResolutionComonadSquareHom_comp.{u, v, w} J a a') (n + 1)
      (squareAlgebraMap.{u, v, w} J a b hsq) (squareAlgebraMap.{u, v, w} J a' b' hsq')
      (squareAlgebraMap.{u, v, w} J (a ≫ a') (b ≫ b') hsq'')
      (Under.UnderMorphism.ext (by
        simp only [Under.comp_right, Under.mapComp_hom_app_right, Under.map_map_right]
        exact Category.comp_id _)))

/-- The termwise maps of standard resolutions are compatible with composition of squares. -/
lemma squareResolutionTermMap_comp (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    (a' : A' ⟶ A'') (b' : B' ⟶ B'') (hsq' : f' ≫ b' = a' ≫ f'')
    (hsq'' : f ≫ b ≫ b' = (a ≫ a') ≫ f'') (n : ℕ) :
    (squareResolutionTermMap.{u, v, w} J a b hsq n).right ≫
        (squareResolutionTermMap.{u, v, w} J a' b' hsq' n).right =
      (squareResolutionTermMap.{u, v, w} J (a ≫ a') (b ≫ b') hsq'' n).right := by
  have key := congrArg Under.Hom.right
    (squareResolutionTermMap_comp_mapComp.{u, v, w} J a b hsq a' b' hsq' hsq'' n)
  rw [Under.comp_right, Under.comp_right, Under.mapComp_hom_app_right,
    Under.map_map_right] at key
  exact key.symm.trans (Category.comp_id _)

end Resolution

section Modules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A A' A'' B B' B'' : Sheaf J CommRingCat.{max u v w}}
  {f : A ⟶ B} {f' : A' ⟶ B'} {f'' : A'' ⟶ B''}

namespace ResolutionSquareMap

variable {J} {a : A ⟶ A'} {b : B ⟶ B'} {a' : A' ⟶ A''} {b' : B' ⟶ B''}

/-- Two maps of standard resolutions over the same square agree when their degreewise maps do. -/
lemma ext {sq sq' : ResolutionSquareMap.{u, v, w} J f f' a b}
    (h : ∀ n, sq.resolution n = sq'.resolution n) : sq = sq' := by
  cases sq
  cases sq'
  congr
  exact funext h

/-- The composite of maps of standard resolutions over two squares `(a, b)` and `(a', b')`: a map
of standard resolutions over the composite square `(a ≫ a', b ≫ b')`. -/
noncomputable def comp (sq₁ : ResolutionSquareMap.{u, v, w} J f f' a b)
    (sq₂ : ResolutionSquareMap.{u, v, w} J f' f'' a' b') :
    ResolutionSquareMap.{u, v, w} J f f'' (a ≫ a') (b ≫ b') where
  resolution n := sq₁.resolution n ≫ sq₂.resolution n
  resolution_base n := by
    rw [← Category.assoc, sq₁.resolution_base, Category.assoc, sq₂.resolution_base,
      Category.assoc]
  resolution_augmentation n := by
    rw [Category.assoc, sq₂.resolution_augmentation, ← Category.assoc,
      sq₁.resolution_augmentation, Category.assoc]
  resolution_naturality g := by
    rw [← Category.assoc, sq₁.resolution_naturality, Category.assoc, sq₂.resolution_naturality,
      Category.assoc]

/-- The degreewise maps of the composite are the composites of the degreewise maps. -/
@[simp]
lemma comp_resolution (sq₁ : ResolutionSquareMap.{u, v, w} J f f' a b)
    (sq₂ : ResolutionSquareMap.{u, v, w} J f' f'' a' b') (n : SimplexCategoryᵒᵖ) :
    (sq₁.comp sq₂).resolution n = sq₁.resolution n ≫ sq₂.resolution n :=
  rfl

end ResolutionSquareMap

/-- **The canonical maps of standard resolutions compose.** For two composable commutative
squares, the composite of the two canonical maps of standard resolutions is, in every degree, the
canonical map of the composite square. -/
theorem resolutionSquareMap_resolution_comp (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    (a' : A' ⟶ A'') (b' : B' ⟶ B'') (hsq' : f' ≫ b' = a' ≫ f'') {a'' : A ⟶ A''}
    {b'' : B ⟶ B''} (ha : a ≫ a' = a'') (hb : b ≫ b' = b'') (hsq'' : f ≫ b'' = a'' ≫ f'')
    (n : SimplexCategoryᵒᵖ) :
    (resolutionSquareMap.{u, v, w} J a b hsq).resolution n ≫
        (resolutionSquareMap.{u, v, w} J a' b' hsq').resolution n =
      (resolutionSquareMap.{u, v, w} J a'' b'' hsq'').resolution n := by
  subst ha hb
  exact squareResolutionTermMap_comp.{u, v, w} J a b hsq a' b' hsq' hsq'' n.unop.len

/-- **The canonical maps of standard resolutions compose**, as maps over the composite square. -/
theorem resolutionSquareMap_comp (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    (a' : A' ⟶ A'') (b' : B' ⟶ B'') (hsq' : f' ≫ b' = a' ≫ f'')
    (hsq'' : f ≫ b ≫ b' = (a ≫ a') ≫ f'') :
    (resolutionSquareMap.{u, v, w} J a b hsq).comp (resolutionSquareMap.{u, v, w} J a' b' hsq') =
      resolutionSquareMap.{u, v, w} J (a ≫ a') (b ≫ b') hsq'' :=
  ResolutionSquareMap.ext fun n =>
    resolutionSquareMap_resolution_comp.{u, v, w} J a b hsq a' b' hsq' rfl rfl hsq'' n

variable {J}

/-- Two morphisms out of the cotangent complex agree when they agree in every degree `-n`. -/
lemma cotangentComplex_hom_ext {K : CochainComplex (targetModules.{u, v, w} J B) ℤ}
    {φ ψ : cotangentComplex.{u, v, w} J f ⟶ K} (h : ∀ n : ℕ, φ.f (-(n : ℤ)) = ψ.f (-(n : ℤ))) :
    φ = ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : i ≤ 0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by lia⟩
    exact h n
  · exact (cotangentComplex_isZero_pos.{u, v, w} J f i (by lia)).eq_of_src _ _

attribute [local instance] moduleOfSections

variable {a : A ⟶ A'} {b : B ⟶ B'} {a' : A' ⟶ A''} {b' : B' ⟶ B''}

/-- The composite of the degreewise maps of two squares carries the universal derivation of `P_n`
to the universal derivation of `P''_n` precomposed with the two maps of standard resolutions. -/
lemma squareCotangentTermMap_comp_d (sq₁ : ResolutionSquareMap.{u, v, w} J f f' a b)
    (sq₂ : ResolutionSquareMap.{u, v, w} J f' f'' a' b') (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J f n).obj.obj U) :
    ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n _
        (squareCotangentTermMap sq₁ n ≫
          (squareRestrict.{u, v, w} J b).map (squareCotangentTermMap sq₂ n))).d x =
      ((cotangentSimplicialModule.{u, v, w} J f'').universalDerivation n).d
        ((sq₂.resolution n).hom.app U ((sq₁.resolution n).hom.app U x)) := by
  rw [squareCotangentTermMap_comp_derivation sq₁ n]
  have hψ := PresheafOfModulesOfCommRing.Derivation.congr_d
    (squareCotangentTermMap_derivation sq₂ n) ((sq₁.resolution n).hom.app U x)
  rwa [(cotangentSimplicialModule.{u, v, w} J f').derivationEquiv_eq_postcomp n
    (squareCotangentTermMap sq₂ n)] at hψ

/-- The degreewise map of base-changed differentials of a composite square is the composite of the
degreewise maps. -/
lemma squareCotangentTermMap_comp (sq₁ : ResolutionSquareMap.{u, v, w} J f f' a b)
    (sq₂ : ResolutionSquareMap.{u, v, w} J f' f'' a' b') (n : SimplexCategoryᵒᵖ) :
    squareCotangentTermMap (sq₁.comp sq₂) n =
      squareCotangentTermMap sq₁ n ≫
        (squareRestrict.{u, v, w} J b).map (squareCotangentTermMap sq₂ n) :=
  (squareCotangentTermMap_unique (sq₁.comp sq₂) n _
    (squareCotangentTermMap_comp_d sq₁ sq₂ n)).symm

/-- In degree `-n`, the composite of the maps of cotangent complexes of two squares is given by
the composite of the degreewise maps, read through the canonical degree isomorphisms. -/
private lemma squareCotangentComplexMap_comp_f {f₂ : A'' ⟶ B''}
    (sq₁ : ResolutionSquareMap.{u, v, w} J f f' a b)
    (sq₂ : ResolutionSquareMap.{u, v, w} J f' f₂ a' b') (n : ℕ) :
    (squareCotangentComplexMap sq₁ ≫
        ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap sq₂)).f (-(n : ℤ)) =
      (cotangentComplex_degreeIso.{u, v, w} J f n).hom ≫
        (squareCotangentTermMap sq₁ (op ⦋n⦌) ≫
          (squareRestrict.{u, v, w} J b).map (squareCotangentTermMap sq₂ (op ⦋n⦌))) ≫
          (squareRestrict.{u, v, w} J b).map ((squareRestrict.{u, v, w} J b').map
            (cotangentComplex_degreeIso.{u, v, w} J f₂ n).inv) := by
  rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    squareCotangentComplexMap_f, squareCotangentComplexMap_f, Category.assoc, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_assoc, Functor.map_comp, Category.assoc]

/-- **The square functoriality of the cotangent complex is compatible with composition.** The map
of cotangent complexes of a composite square is the map of the first square followed by the
restriction of scalars of the map of the second. -/
theorem squareCotangentComplexMap_comp (sq₁ : ResolutionSquareMap.{u, v, w} J f f' a b)
    (sq₂ : ResolutionSquareMap.{u, v, w} J f' f'' a' b') :
    squareCotangentComplexMap (sq₁.comp sq₂) =
      squareCotangentComplexMap sq₁ ≫
        ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap sq₂) := by
  refine cotangentComplex_hom_ext fun n => ?_
  rw [squareCotangentComplexMap_comp_f, squareCotangentComplexMap_f,
    squareCotangentTermMap_comp]
  rfl

/-- **The canonical maps of cotangent complexes compose.** For two composable commutative
squares, the map of cotangent complexes attached to the composite square is the map of the first
square followed by the restriction of scalars of the map of the second. -/
theorem squareCotangentComplexMap_resolutionSquareMap_comp (hsq : f ≫ b = a ≫ f')
    (hsq' : f' ≫ b' = a' ≫ f'') (hsq'' : f ≫ b ≫ b' = (a ≫ a') ≫ f'') :
    squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J (a ≫ a') (b ≫ b') hsq'') =
      squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq) ≫
        ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a' b' hsq')) := by
  rw [← resolutionSquareMap_comp.{u, v, w} J a b hsq a' b' hsq' hsq'',
    squareCotangentComplexMap_comp]

/-- The degreewise map of base-changed differentials of a square `(a'', b)` whose map of
standard resolutions is the composite of those of a square `(a, b)` and of a square `(a', 𝟙)`
is the composite of the two degreewise maps. -/
lemma squareCotangentTermMap_eq_comp_of_id {a' : A' ⟶ A''} {a'' : A ⟶ A''}
    (sq₁ : ResolutionSquareMap.{u, v, w} J f f' a b)
    {f₂ : A'' ⟶ B'} (sq₂ : ResolutionSquareMap.{u, v, w} J f' f₂ a' (𝟙 B'))
    (sq : ResolutionSquareMap.{u, v, w} J f f₂ a'' b)
    (h : ∀ n, sq.resolution n = sq₁.resolution n ≫ sq₂.resolution n) (n : SimplexCategoryᵒᵖ) :
    squareCotangentTermMap sq n =
      squareCotangentTermMap sq₁ n ≫
        (squareRestrict.{u, v, w} J b).map (squareCotangentTermMap sq₂ n) :=
  (squareCotangentTermMap_unique sq n _ fun U x =>
    (squareCotangentTermMap_comp_d sq₁ sq₂ n U x).trans (by rw [h]; rfl)).symm

/-- The map of cotangent complexes of a square `(a'', b)` whose map of standard resolutions is
the composite of those of a square `(a, b)` and of a square `(a', 𝟙)` is the composite of the
two maps of cotangent complexes. -/
theorem squareCotangentComplexMap_eq_comp_of_id {a' : A' ⟶ A''} {a'' : A ⟶ A''}
    (sq₁ : ResolutionSquareMap.{u, v, w} J f f' a b)
    {f₂ : A'' ⟶ B'} (sq₂ : ResolutionSquareMap.{u, v, w} J f' f₂ a' (𝟙 B'))
    (sq : ResolutionSquareMap.{u, v, w} J f f₂ a'' b)
    (h : ∀ n, sq.resolution n = sq₁.resolution n ≫ sq₂.resolution n) :
    squareCotangentComplexMap sq =
      squareCotangentComplexMap sq₁ ≫
        ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap sq₂) := by
  refine cotangentComplex_hom_ext fun n => ?_
  rw [squareCotangentComplexMap_comp_f, squareCotangentComplexMap_f,
    squareCotangentTermMap_eq_comp_of_id sq₁ sq₂ sq h]
  rfl

/-- Changing the target homomorphism of a square along an equality `f₁ = f₂` changes the map of
cotangent complexes by the corresponding identification `L_{f₁} = L_{f₂}`. -/
lemma squareCotangentComplexMap_resolutionSquareMap_eqToHom {f₁ f₂ : A' ⟶ B'} (e : f₁ = f₂)
    (hsq₁ : f ≫ b = a ≫ f₁) (hsq₂ : f ≫ b = a ≫ f₂) :
    squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq₁) ≫
        ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (eqToHom (congrArg (cotangentComplex.{u, v, w} J) e)) =
      squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq₂) := by
  subst e
  simp

end Modules

section Tower

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- The unit `x ↦ 1 ⊗ x` of extension–restriction of scalars along `h : B ⟶ D`, on the cotangent
simplicial module of `g : A ⟶ B`: the map to the restriction of scalars of its degreewise base
change. -/
noncomputable def towerCotangentUnitSimplicial :
    (cotangentSimplicialModule.{u, v, w} J g).object ⟶
      ((SimplicialObject.whiskering _ _).obj (squareRestrict.{u, v, w} J h)).obj
        (baseChangedCotangentSimplicialModule.{u, v, w} J g h) :=
  Functor.whiskerLeft (cotangentSimplicialModule.{u, v, w} J g).object
    (towerExtendRestrictAdjunction.{u, v, w} J h).unit

/-- The unit of extension–restriction of scalars along `h : B ⟶ D` on the alternating-face-map
complex of the cotangent simplicial module of `g : A ⟶ B`. -/
noncomputable def towerCotangentUnitMoore :
    (AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
        (cotangentSimplicialModule.{u, v, w} J g).object ⟶
      ((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J D)).obj
          (baseChangedCotangentSimplicialModule.{u, v, w} J g h)) :=
  (AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J B)).map
      (towerCotangentUnitSimplicial.{u, v, w} J g h) ≫
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
        (squareRestrict.{u, v, w} J h)).app
      (baseChangedCotangentSimplicialModule.{u, v, w} J g h)).inv

/-- In degree `n` the unit on alternating-face-map complexes is the unit of
extension–restriction of scalars. -/
@[simp]
lemma towerCotangentUnitMoore_f (n : ℕ) :
    (towerCotangentUnitMoore.{u, v, w} J g h).f n =
      (towerExtendRestrictAdjunction.{u, v, w} J h).unit.app
        ((cotangentSimplicialModule.{u, v, w} J g).object.obj (op ⦋n⦌)) :=
  Category.comp_id _

/-- The unit of extension–restriction of scalars along `h : B ⟶ D` on the cotangent complex of
`g : A ⟶ B`: the `B`-linear map `L_{B/A} ⟶ L_{B/A} ⊗_B D`, degreewise `x ↦ 1 ⊗ x`, into the
first vertex of the triangle of Tag 08SZ read over `B`. -/
noncomputable def towerCotangentUnit :
    cotangentComplex.{u, v, w} J g ⟶
      ((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (baseChangedCotangentComplex.{u, v, w} J g h) :=
  HomologicalComplex.extendMap (towerCotangentUnitMoore.{u, v, w} J g h)
      (ComplexShape.embeddingUpIntLE 0) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (squareRestrict.{u, v, w} J h)
      ((AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J D)).obj
        (baseChangedCotangentSimplicialModule.{u, v, w} J g h))
      (ComplexShape.embeddingUpIntLE 0)).hom

/-- In cohomological degree `-n` the unit on cotangent complexes is the unit of
extension–restriction of scalars, read through the two canonical degree isomorphisms. -/
lemma towerCotangentUnit_f (n : ℕ) :
    (towerCotangentUnit.{u, v, w} J g h).f (-(n : ℤ)) =
      (cotangentComplex_degreeIso.{u, v, w} J g n).hom ≫
        (towerExtendRestrictAdjunction.{u, v, w} J h).unit.app
          ((cotangentSimplicialModule.{u, v, w} J g).object.obj (op ⦋n⦌)) ≫
          (squareRestrict.{u, v, w} J h).map
            (baseChangedCotangentComplex_degreeIso.{u, v, w} J g h n).inv := by
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  simp only [towerCotangentUnit, cotangentComplex,
    HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ _ _ hn,
    towerCotangentUnitMoore_f, cotangentComplex_degreeIso, baseChangedCotangentComplex,
    baseChangedCotangentComplex_degreeIso]

/-- **The first arrow of Tag 08SZ is the transpose of the square functoriality.** The unit
`L_{B/A} ⟶ L_{B/A} ⊗_B D` followed by the restriction of scalars of the first arrow
`L_{B/A} ⊗_B D ⟶ L_{D/A}` is the map of cotangent complexes attached to the square `(𝟙 A, h)`. -/
theorem towerCotangentUnit_comp_towerCotangentBaseChange :
    towerCotangentUnit.{u, v, w} J g h ≫
        ((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (towerCotangentBaseChange.{u, v, w} J g h) =
      squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h) := by
  refine cotangentComplex_hom_ext fun n => ?_
  rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, towerCotangentUnit_f,
    towerCotangentBaseChange_f, squareCotangentComplexMap_f, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    Functor.map_id, Category.id_comp, ← Category.assoc
      ((towerExtendRestrictAdjunction.{u, v, w} J h).unit.app _),
    baseChangeSimplicialMap_transpose]

end Tower

section TowerFactorisation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A₀ B₀ A B : Sheaf J CommRingCat.{max u v w}}
  {g : A₀ ⟶ B₀} {a : A ⟶ B} {α : A₀ ⟶ A} {β : B₀ ⟶ B}

/-- **The square functoriality through the two arrows of Tag 08SZ.** For a commutative square
`g ≫ β = α ≫ a` the map of cotangent complexes `L_{B₀/A₀} ⟶ L_{B/A}` attached to it factors as
the unit `L_{B₀/A₀} ⟶ L_{B₀/A₀} ⊗_{B₀} B`, followed by the restriction of scalars along `β` of
the first arrow `L_{B₀/A₀} ⊗_{B₀} B ⟶ L_{B/A₀}` of the tower `A₀ ⟶ B₀ ⟶ B`, the identification
`L_{g ≫ β} = L_{α ≫ a}`, and the second arrow `L_{B/A₀} ⟶ L_{B/A}` of the tower
`A₀ ⟶ A ⟶ B`. -/
theorem squareCotangentComplexMap_eq_towerCotangent (hsq : g ≫ β = α ≫ a) :
    towerCotangentUnit.{u, v, w} J g β ≫
        ((squareRestrict.{u, v, w} J β).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (towerCotangentBaseChange.{u, v, w} J g β ≫
            eqToHom (congrArg (cotangentComplex.{u, v, w} J) hsq) ≫
              towerCotangentChangeOfBase.{u, v, w} J α a) =
      squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J α β hsq) := by
  have hC := squareCotangentComplexMap_eq_comp_of_id
    (resolutionSquareMap.{u, v, w} J (𝟙 A₀) β (by rw [hsq, Category.id_comp]))
    (resolutionSquareMap.{u, v, w} J α (𝟙 B) (by rw [Category.comp_id]))
    (resolutionSquareMap.{u, v, w} J α β hsq)
    (fun n => (resolutionSquareMap_resolution_comp.{u, v, w} J _ _ _ _ _ _
      (Category.id_comp α) (Category.comp_id β) hsq n).symm)
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
    towerCotangentUnit_comp_towerCotangentBaseChange, ← Category.assoc,
    squareCotangentComplexMap_resolutionSquareMap_eqToHom hsq _
      (by rw [hsq, Category.id_comp])]
  exact hC.symm

end TowerFactorisation

end CategoryTheory.Sheaf
